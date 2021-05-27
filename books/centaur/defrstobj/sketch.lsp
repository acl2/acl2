; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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
; Sketch of abstract stobj correspondence for defrstobj
; Original author: Sol Swords <sswords@centtech.com>


(in-package "RSTOBJ")


;; This book was a sketch of how the abstract stobj-based implementation of
;; defrstobj would work.  It might be useful as documentation, but shouldn't
;; ever need to be included.  It may not stay up to date with changes to
;; defabsstobj.

(local (include-book "generic"))

(include-book "tools/rulesets" :dir :system)
(include-book "misc/records" :dir :system)
;; (include-book "clause-processors/generalize" :dir :system)
;; (include-book "clause-processors/find-subterms" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/lists/resize-list" :dir :system)
(include-book "std/stobjs/absstobjs" :dir :system)

(include-book "arithmetic/top-with-meta" :dir :system)


(include-book "def-typed-record")
(include-book "misc/records" :dir :system)


(defun ubp-listp (n x)
  (declare (xargs :guard t))
  (if (atom x)
      (not x)
    (and (unsigned-byte-p n (car x))
         (ubp-listp n (cdr x)))))

(defun ubp-fix (n x)
  (declare (xargs :guard t))
  (if (unsigned-byte-p n x)
      x
    0))

(def-typed-record ubp8
  :elem-p       (unsigned-byte-p 8 x)
  :elem-list-p  (ubp-listp 8 x)
  :elem-default 0
  :elem-fix     (ubp-fix 8 x))


(defun nonneg-fix (x)
  (declare (xargs :guard t))
  (if (integerp x)
      (if (< x 0)
          (- x)
        x)
    0))

(def-typed-record nonneg
  :elem-p (natp x)
  :elem-list-p (nat-listp x)
  :elem-default 0
  :elem-fix (nonneg-fix x))




#||
(defrstobj st

  (natarr  :type (array (integer 0 *) (32))
           :initially 0
           :typed-record nonneg-tr-p)

  (u8arr   :type (array (unsigned-byte 8) (64))
           :initially 0
           :typed-record ubp8-tr-p
           :resizable t)

  (intfld  :type integer
           :initially 5
           :fix (ifix x))

  (natfld :type (integer 0 *)
          :initially 0
          :fix (nonneg-fix x)))


(include-book "defrstobj")

(defrstobj st1

  (natarr1  :type (array (integer 0 *) (32))
            :initially 0
            :typed-record nonneg-tr-p)

  (u8arr1   :type (array (unsigned-byte 8) (64))
            :initially 0
            :typed-record ubp8-tr-p)

  (intfld1  :type integer
            :initially 5)

  (natfld1 :type (integer 0 *)
           :initially 0))

||#


;; (make-event
;;  `(encapsulate nil

;;     (local (defthm plus-collect-consts
;;              (implies (syntaxp (and (quotep x) (quotep y)))
;;                       (equal  (+ x y z)
;;                               (+ (+ x y) z)))))

;;     (local (defthm rstobj-fix-idempotent-for-st-intfld
;;              (implies (type-p integer x)
;;                       (equal (ifix x) x))))

;;     (local (defthm rstobj-fix-idempotent-for-st-natfld
;;              (implies (type-p (integer 0 *) x)
;;                       (equal (nonneg-fix x) x))))

;;     (local (in-theory (e/d**
;;                        ((:t nfix)
;;                         natp-compound-recognizer
;;                         zp-compound-recognizer
;;                         field-map-key-lookup
;;                         plus-collect-consts
;;                         nth-of-repeat
;;                         len-of-repeat
;;                         append-to-nil
;;                         (:t repeat)
;;                         make-list-ac-removal
;;                         nth-when-atom
;;                         nth-0-cons
;;                         nth-add1
;;                         car-cons cdr-cons
;;                         nfix-when-natp
;;                         length
;;                         len-of-cons
;;                         len-when-atom
;;                         update-nth-array
;;                         nth-update-nth
;;                         len-update-nth
;;                         max
;;                         (:t len)
;;                         resize-list-when-zp
;;                         (:rules-of-class :executable-counterpart :here)

;;                         rstobj-fix-idempotent-for-st-intfld
;;                         rstobj-fix-idempotent-for-st-natfld

;;                         ,@(cdr (assoc :theorems
;;                                       (cdr (assoc 'nonneg-tr-p
;;                                                   (table-alist 'rstobj::typed-records
;;                                                                (w state))))))
;;                         ,@(cdr (assoc :theorems
;;                                       (cdr (assoc 'ubp8-tr-p
;;                                                   (table-alist 'rstobj::typed-records
;;                                                                (w state)))))))
;;                        ((make-list-ac)
;;                         (repeat)))))

;;     (defstobj st$c
;;       (natarr$c  :type (array (integer 0 *) (32))
;;                  :initially 0)

;;       (u8arr$c   :type (array (unsigned-byte 8) (64))
;;                  :initially 0
;;                  :resizable t)

;;       (intfld$c  :type integer
;;                  :initially 5)

;;       (natfld$c :type (integer 0 *)
;;                 :initially 0))


;;     (defun empty-u8arr$c (st$c)
;;       (declare (xargs :stobjs st$c))
;;       (resize-u8arr$c 0 st$c))


;;     (defun stp$a (st$a)
;;       (declare (xargs :guard t)
;;                (ignorable st$a))
;;       t)

;;     (defun create-st$a ()
;;       (declare (xargS :guard t))
;;       (let* ((st$a nil)
;;              (st$a (s :natarr nil st$a))
;;              (st$a (s :natarr-length 32 st$a))
;;              (st$a (s :u8arr nil st$a))
;;              (st$a (s :u8arr-length 64 st$a))
;;              (st$a (s :intfld 5 st$a))
;;              (st$a (s :natfld 0 st$a)))
;;         st$a))

;;     (defun natarr-length$a (st$a)
;;       (declare (xargs :guard t))
;;       (nfix (g :natarr-length st$a)))

;;     (defun get-natarr$a (i st$a)
;;       (declare (xargs :guard (and (natp i)
;;                                   (< i (natarr-length$a st$a)))))
;;       (nonneg-tr-get i (g :natarr st$a)))

;;     (defun set-natarr$a (i v st$a)
;;       (declare (xargs :guard (and (natp i)
;;                                   (< i (natarr-length$a st$a))
;;                                   (natp v))))
;;       (let* ((tr (g :natarr st$a))
;;              (tr (nonneg-tr-set i v tr)))
;;         (s :natarr tr st$a)))



;;     (defun u8arr-length$a (st$a)
;;       (declare (xargs :guard t))
;;       (nfix (g :u8arr-length st$a)))

;;     (defun get-u8arr$a (i st$a)
;;       (declare (xargs :guard (and (natp i)
;;                                   (< i (u8arr-length$a st$a)))))
;;       (ubp8-tr-get i (g :u8arr st$a)))

;;     (defun set-u8arr$a (i v st$a)
;;       (declare (xargs :guard (and (natp i)
;;                                   (< i (u8arr-length$a st$a))
;;                                   (unsigned-byte-p 8 v))))
;;       (let* ((tr (g :u8arr st$a))
;;              (tr (ubp8-tr-set i v tr)))
;;         (s :u8arr tr st$a)))

;;     (defun resize-u8arr$a (n st$a)
;;       (declare (xargs :guard (and (natp n)
;;                                   (<= (u8arr-length$a st$a) n))))
;;       (s :u8arr-length n st$a))

;;     (defun empty-u8arr$a (st$a)
;;       (declare (xargs :guard t))
;;       (let* ((st$a (s :u8arr-length 0 st$a)))
;;         (s :u8arr nil st$a)))

;;     (defun get-intfld$a (st$a)
;;       (declare (xargs :guard t))
;;       (ifix (g :intfld st$a)))

;;     (defun set-intfld$a (v st$a)
;;       (declare (xargs :guard (integerp v)))
;;       (s :intfld v st$a))

;;     (defun get-natfld$a (st$a)
;;       (declare (xargs :guard t))
;;       (nonneg-fix (g :natfld st$a)))

;;     (defun set-natfld$a (v st$a)
;;       (declare (xargs :guard (natp v)))
;;       (s :natfld v st$a))


;;     (local
;;      (progn
;;        (defconst *rstobj-tmp-field-map*
;;          (list (make-array-fieldinfo :tr-key :natarr :size-key :natarr-length)
;;                (make-array-fieldinfo :tr-key :u8arr :size-key :u8arr-length)
;;                (make-scalar-fieldinfo :key :intfld)
;;                (make-scalar-fieldinfo :key :natfld)))

;;        (defund rstobj-tmp-field-map () *rstobj-tmp-field-map*)

;;        (defun rstobj-tmp-tr-get (name i tr)
;;          (case name
;;            (:natarr (nonneg-tr-get i tr))
;;            (:u8arr (ubp8-tr-get i tr))))

;;        (defun rstobj-tmp-tr-set (name i v tr)
;;          (case name
;;            (:natarr (nonneg-tr-set i v tr))
;;            (:u8arr (ubp8-tr-set i v tr))))

;;        (defun rstobj-tmp-tr-fix (name v)
;;          (case name
;;            (:natarr (nonneg-fix v))
;;            (:u8arr (ubp-fix 8 v))))

;;        (defun rstobj-tmp-tr-elem-p (name v)
;;          (case name
;;            (:natarr (natp v))
;;            (:u8arr (unsigned-byte-p 8 v))))

;;        (defun rstobj-tmp-scalar-fix (name v)
;;          (case name
;;            (:intfld (ifix v))
;;            (:natfld (nonneg-fix v))))

;;        (defun rstobj-tmp-scalar-elem-p (name v)
;;          (case name
;;            (:intfld (integerp v))
;;            (:natfld (natp v))))

;;        (defun-sk rstobj-tmp-field-corr (st$c st$a)
;;          (forall (idx i)
;;                  (let ((entry (nth idx (rstobj-tmp-field-map))))
;;                    (and (implies (equal (tag entry) :array)
;;                                  ;; array
;;                                  (b* (((array-fieldinfo x) entry)
;;                                       (arr (nth idx st$c))
;;                                       (tr  (g x.tr-key st$a)))
;;                                    (and (implies (natp i)
;;                                                  (equal (rstobj-tmp-tr-get x.tr-key i tr)
;;                                                         (if (< i (len arr))
;;                                                             (nth i arr)
;;                                                           (rstobj-tmp-tr-fix x.tr-key nil))))
;;                                         (equal (g x.size-key st$a)
;;                                                (len arr)))))
;;                         (implies (equal (tag entry) :scalar)
;;                                  (b* (((scalar-fieldinfo x) entry))
;;                                    (equal (g x.key st$a)
;;                                           (nth idx st$c)))))))
;;          :rewrite :direct)

;;        (in-theory (disable rstobj-tmp-field-corr rstobj-tmp-field-corr-necc))


;;        (defthm rstobj-tmp-field-corr-of-size-key
;;          (mv-let (keytype idx)
;;            (field-map-key-lookup szkey (rstobj-tmp-field-map))
;;            (implies (and (rstobj-tmp-field-corr st$c st$a)
;;                          (equal keytype :size))
;;                     (equal (g szkey st$a)
;;                            (len (nth idx st$c)))))
;;          :hints (("goal" :by (:instance
;;                               (:functional-instance
;;                                rstobj-field-corr-of-size-key
;;                                (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
;;                                (rstobj-field-corr rstobj-tmp-field-corr)
;;                                (rstobj-field-map rstobj-tmp-field-map)
;;                                (rstobj-tr-get rstobj-tmp-tr-get)
;;                                (rstobj-tr-set rstobj-tmp-tr-set)
;;                                (rstobj-tr-fix rstobj-tmp-tr-fix)
;;                                (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
;;                                (rstobj-scalar-fix rstobj-tmp-scalar-fix)
;;                                (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
;;                               (rstobj$c st$c)
;;                               (rstobj$a st$a))
;;                   :in-theory (disable (rstobj-tmp-field-map))
;;                   :do-not-induct t)
;;                  (let ((lit (car clause)))
;;                    (case-match lit
;;                      ((f ('rstobj-tmp-field-corr . &) . &)
;;                       `(:in-theory (e/d ,(if (eq f 'equal)
;;                                              '(rstobj-tmp-field-corr)
;;                                            '(rstobj-tmp-field-corr-necc))
;;                                         ((rstobj-tmp-field-map)
;;                                          rstobj-tmp-tr-get
;;                                          rstobj-tmp-tr-fix
;;                                          rstobj-tmp-scalar-fix))))
;;                      (& '(:in-theory (enable (rstobj-tmp-field-map))))))))

;;        (defthm rstobj-tmp-field-corr-of-scalar-key
;;          (mv-let (keytype idx)
;;            (field-map-key-lookup sckey (rstobj-tmp-field-map))
;;            (implies (and (rstobj-tmp-field-corr st$c st$a)
;;                          (equal keytype :scalar))
;;                     (equal (g sckey st$a)
;;                            (nth idx st$c))))
;;          :hints (("goal" :by (:instance
;;                               (:functional-instance
;;                                rstobj-field-corr-of-scalar-key
;;                                (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
;;                                (rstobj-field-corr rstobj-tmp-field-corr)
;;                                (rstobj-field-map rstobj-tmp-field-map)
;;                                (rstobj-tr-get rstobj-tmp-tr-get)
;;                                (rstobj-tr-set rstobj-tmp-tr-set)
;;                                (rstobj-tr-fix rstobj-tmp-tr-fix)
;;                                (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
;;                                (rstobj-scalar-fix rstobj-tmp-scalar-fix)
;;                                (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
;;                               (rstobj$c st$c)
;;                               (rstobj$a st$a))
;;                   :do-not-induct t)))

;;        (defthm rstobj-tmp-field-corr-of-tr-key
;;          (mv-let (keytype idx)
;;            (field-map-key-lookup trkey (rstobj-tmp-field-map))
;;            (implies (and (rstobj-tmp-field-corr st$c st$a)
;;                          (equal keytype :array)
;;                          (natp i))
;;                     (equal (rstobj-tmp-tr-get trkey i (g trkey st$a))
;;                            (if (< i (len (nth idx st$c)))
;;                                (nth i (nth idx st$c))
;;                              (rstobj-tmp-tr-fix trkey nil)))))
;;          :hints (("goal" :by (:instance
;;                               (:functional-instance
;;                                rstobj-field-corr-of-tr-key
;;                                (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
;;                                (rstobj-field-corr rstobj-tmp-field-corr)
;;                                (rstobj-field-map rstobj-tmp-field-map)
;;                                (rstobj-tr-get rstobj-tmp-tr-get)
;;                                (rstobj-tr-set rstobj-tmp-tr-set)
;;                                (rstobj-tr-fix rstobj-tmp-tr-fix)
;;                                (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
;;                                (rstobj-scalar-fix rstobj-tmp-scalar-fix)
;;                                (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
;;                               (rstobj$c st$c)
;;                               (rstobj$a st$a))
;;                   :do-not-induct t)))


;;        (defthm rstobj-tmp-field-corr-of-tr-key-elaborate
;;          (mv-let (keytype idx)
;;            (field-map-key-lookup trkey (rstobj-tmp-field-map))
;;            (implies (and (rstobj-tmp-field-corr st$c st$a)
;;                          (equal keytype :array)
;;                          (natp i))
;;                     (and (implies (equal trkey :natarr)
;;                                   (equal (nonneg-tr-get i (g trkey st$a))
;;                                          (if (< i (len (nth idx st$c)))
;;                                              (nth i (nth idx st$c))
;;                                            (rstobj-tmp-tr-fix trkey nil))))
;;                          (implies (equal trkey :u8arr)
;;                                   (equal (ubp8-tr-get i (g trkey st$a))
;;                                          (if (< i (len (nth idx st$c)))
;;                                              (nth i (nth idx st$c))
;;                                            (rstobj-tmp-tr-fix trkey nil)))))))
;;          :hints (("goal" :use rstobj-tmp-field-corr-of-tr-key
;;                   :in-theory (e/d (rstobj-tmp-tr-get) (rstobj-tmp-field-corr-of-tr-key)))))


;;        (defthm rstobj-tmp-field-corr-of-update-scalar
;;          (implies (and (rstobj-tmp-field-corr st$c st$a)
;;                        (equal (tag (nth idx (rstobj-tmp-field-map))) :scalar)
;;                        (equal (scalar-fieldinfo->key (nth idx (rstobj-tmp-field-map))) key)
;;                        (equal v (rstobj-tmp-scalar-fix key v)))
;;                   (rstobj-tmp-field-corr (update-nth idx v st$c)
;;                                          (s key v st$a)))
;;          :hints (("goal" :by (:instance
;;                               (:functional-instance
;;                                rstobj-field-corr-of-update-scalar
;;                                (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
;;                                (rstobj-field-corr rstobj-tmp-field-corr)
;;                                (rstobj-field-map rstobj-tmp-field-map)
;;                                (rstobj-tr-get rstobj-tmp-tr-get)
;;                                (rstobj-tr-set rstobj-tmp-tr-set)
;;                                (rstobj-tr-fix rstobj-tmp-tr-fix)
;;                                (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
;;                                (rstobj-scalar-fix rstobj-tmp-scalar-fix)
;;                                (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
;;                               (rstobj$c st$c)
;;                               (rstobj$a st$a))
;;                   :do-not-induct t)))




;;        (defthm rstobj-tmp-field-corr-of-update-array
;;          (implies (and (rstobj-tmp-field-corr st$c st$a)
;;                        (equal (tag (nth idx (rstobj-tmp-field-map))) :array)
;;                        (equal (array-fieldinfo->tr-key (nth idx (rstobj-tmp-field-map))) key)
;;                        (equal tr1 (rstobj-tmp-tr-set key i v (g key st$a)))
;;                        (equal v (rstobj-tmp-tr-fix key v))
;;                        (natp i)
;;                        (< i (len (nth idx st$c))))
;;                   (rstobj-tmp-field-corr (update-nth idx (update-nth i v (nth idx st$c))
;;                                                      st$c)
;;                                          (s key tr1 st$a)))
;;          :hints (("goal" :by (:instance
;;                               (:functional-instance
;;                                rstobj-field-corr-of-update-array
;;                                (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
;;                                (rstobj-field-corr rstobj-tmp-field-corr)
;;                                (rstobj-field-map rstobj-tmp-field-map)
;;                                (rstobj-tr-get rstobj-tmp-tr-get)
;;                                (rstobj-tr-set rstobj-tmp-tr-set)
;;                                (rstobj-tr-fix rstobj-tmp-tr-fix)
;;                                (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
;;                                (rstobj-scalar-fix rstobj-tmp-scalar-fix)
;;                                (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
;;                               (rstobj$c st$c)
;;                               (rstobj$a st$a))
;;                   :do-not-induct t)))


;;        (defthm rstobj-tmp-field-corr-of-grow-array
;;          (implies (and (rstobj-tmp-field-corr st$c st$a)
;;                        (equal (tag (nth idx (rstobj-tmp-field-map))) :array)
;;                        (equal (array-fieldinfo->size-key (nth idx (rstobj-tmp-field-map))) size-key)
;;                        (natp new-size)
;;                        (<= (len (nth idx st$c)) new-size)
;;                        (equal default (rstobj-tmp-tr-fix
;;                                        (array-fieldinfo->tr-key (nth idx (rstobj-tmp-field-map)))
;;                                        nil)))
;;                   (rstobj-tmp-field-corr (update-nth idx
;;                                                      (resize-list (nth idx st$c) new-size default)
;;                                                      st$c)
;;                                          (s size-key new-size st$a)))
;;          :hints (("goal" :by (:instance
;;                               (:functional-instance
;;                                rstobj-field-corr-of-grow-array
;;                                (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
;;                                (rstobj-field-corr rstobj-tmp-field-corr)
;;                                (rstobj-field-map rstobj-tmp-field-map)
;;                                (rstobj-tr-get rstobj-tmp-tr-get)
;;                                (rstobj-tr-set rstobj-tmp-tr-set)
;;                                (rstobj-tr-fix rstobj-tmp-tr-fix)
;;                                (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
;;                                (rstobj-scalar-fix rstobj-tmp-scalar-fix)
;;                                (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
;;                               (rstobj$c st$c)
;;                               (rstobj$a st$a))
;;                   :do-not-induct t)))

;;        (defthm rstobj-tmp-field-corr-of-empty-array
;;          (implies (and (rstobj-tmp-field-corr st$c st$a)
;;                        (equal (tag (nth idx (rstobj-tmp-field-map))) :array)
;;                        (equal (array-fieldinfo->tr-key (nth idx (rstobj-tmp-field-map))) tr-key)
;;                        (equal (array-fieldinfo->size-key (nth idx (rstobj-tmp-field-map))) size-key))
;;                   (rstobj-tmp-field-corr (update-nth idx nil st$c)
;;                                          (s tr-key nil (s size-key 0 st$a))))
;;          :hints (("goal" :by (:instance
;;                               (:functional-instance
;;                                rstobj-field-corr-of-empty-array
;;                                (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
;;                                (rstobj-field-corr rstobj-tmp-field-corr)
;;                                (rstobj-field-map rstobj-tmp-field-map)
;;                                (rstobj-tr-get rstobj-tmp-tr-get)
;;                                (rstobj-tr-set rstobj-tmp-tr-set)
;;                                (rstobj-tr-fix rstobj-tmp-tr-fix)
;;                                (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
;;                                (rstobj-scalar-fix rstobj-tmp-scalar-fix)
;;                                (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
;;                               (rstobj$c st$c)
;;                               (rstobj$a st$a))
;;                   :do-not-induct t)))


;;        (defthm rstobj-tmp-field-corr-of-create
;;          (rstobj-tmp-field-corr (create-st$c) (create-st$a))
;;          :hints(("Goal" :in-theory (e/d (rstobj-tmp-field-corr))
;;                  :expand ((:free (a b c) (nth a (cons b c)))))))


;;        (defun-nx rstobj-tmp-corr (st$c st$a)
;;          (and (st$cp st$c)
;;               (rstobj-tmp-field-corr st$c st$a)))

;;        (defthm field-lookup-in-rstobj-tmp-field-map
;;          (implies (syntaxp (quotep key))
;;                   (equal (field-map-key-lookup key (rstobj-tmp-field-map))
;;                          (field-map-key-lookup key *rstobj-tmp-field-map*))))

;;        (defthm index-lookup-in-rstobj-tmp-field-map
;;          (implies (syntaxp (quotep idx))
;;                   (equal (nth idx (rstobj-tmp-field-map))
;;                          (nth idx *rstobj-tmp-field-map*))))



;;        (defthm natarr$cp-of-repeat
;;          (implies (natp v)
;;                   (natarr$cp (repeat v n)))
;;          :hints(("Goal" :in-theory (enable repeat natarr$cp)
;;                  :induct (repeat 0 n))))

;;        (defthm natarr$cp-of-update-nth
;;          (implies (and (natp v)
;;                        (natarr$cp x)
;;                        (<= (nfix i) (len x)))
;;                   (natarr$cp (update-nth i v x)))
;;          :hints(("Goal" :in-theory (enable natarr$cp update-nth len))))

;;        (defthm natarr$cp-of-resize-list
;;          (implies (and (natp v)
;;                        (natarr$cp x))
;;                   (natarr$cp (resize-list x n v)))
;;          :hints(("Goal" :in-theory (enable resize-list))))

;;        (defthm u8arr$cp-of-repeat
;;          (implies (unsigned-byte-p 8 v)
;;                   (u8arr$cp (repeat v n)))
;;          :hints(("Goal" :in-theory (enable repeat u8arr$cp)
;;                  :induct (repeat 0 n))))

;;        (defthm u8arr$cp-of-update-nth
;;          (implies (and (unsigned-byte-p 8 v)
;;                        (u8arr$cp x)
;;                        (<= (nfix i) (len x)))
;;                   (u8arr$cp (update-nth i v x)))
;;          :hints(("Goal" :in-theory (enable u8arr$cp update-nth len))))

;;        (defthm u8arr$cp-of-resize-list
;;          (implies (and (unsigned-byte-p 8 v)
;;                        (u8arr$cp x))
;;                   (u8arr$cp (resize-list x n v)))
;;          :hints(("Goal" :in-theory (enable resize-list))))


;;        ;; (local (defthm nonneg-fix-when-natp
;;        ;;            (implies (natp x)
;;        ;;                     (equal (nonneg-fix x) x))))


;;        ;; (local (defthm ifix-when-integerp
;;        ;;          (implies (integerp x)
;;        ;;                   (equal (ifix x) x))))


;;        (set-default-hints
;;         '((and stable-under-simplificationp
;;                '(:in-theory (enable create-st$a create-st$c st$cp)))))))


;;     (local (in-theory (disable
;;                        (rstobj-tmp-field-corr)
;;                        (rstobj-tmp-field-map)
;;                        st$cp
;;                        create-st$a
;;                        (create-st$a)
;;                        create-st$c
;;                        (create-st$c))))

;;     (defabsstobj-events st
;;       :concrete st$c
;;       :corr-fn rstobj-tmp-corr
;;       :creator (create-st :logic create-st$a :exec create-st$c)
;;       :recognizer (stp :logic stp$a :exec st$cp)
;;       :exports
;;       ((natarr-length :logic natarr-length$a :exec natarr$c-length)
;;        (get-natarr :logic get-natarr$a :exec natarr$ci)
;;        (set-natarr :logic set-natarr$a :exec update-natarr$ci)
;;        (u8arr-length :logic u8arr-length$a :exec u8arr$c-length)
;;        (get-u8arr :logic get-u8arr$a :exec u8arr$ci)
;;        (set-u8arr :logic set-u8arr$a :exec update-u8arr$ci)
;;        (resize-u8arr :logic resize-u8arr$a :exec resize-u8arr$c)
;;        (empty-u8arr :logic empty-u8arr$a :exec empty-u8arr$c)
;;        (get-intfld :logic get-intfld$a :exec intfld$c)
;;        (set-intfld :logic set-intfld$a :exec update-intfld$c)
;;        (get-natfld :logic get-natfld$a :exec natfld$c)
;;        (set-natfld :logic set-natfld$a :exec update-natfld$c)))))





(with-output :off (event prove)
  :summary-off (:other-than acl2::form time)
  (make-event
   `(encapsulate nil

      (local (defthm plus-collect-consts
               (implies (syntaxp (and (quotep x) (quotep y)))
                        (equal  (+ x y z)
                                (+ (+ x y) z)))))

      (local (defthm rstobj-fix-idempotent-for-st-intfld
               (implies ,(translate-declaration-to-guard 'integer 'x (w state))
                        (equal (ifix x) x))))

      (local (defthm rstobj-fix-idempotent-for-st-natfld
               (implies ,(translate-declaration-to-guard '(integer 0 *) 'x (w state))
                        (equal (nonneg-fix x) x))))

      (local (in-theory #!acl2
                        (e/d**
                         ((:t nfix)
                          natp-compound-recognizer
                          zp-compound-recognizer
                          nth-of-repeat
                          len-of-repeat
                          append-to-nil
                          (:t repeat)
                          make-list-ac-removal
                          nth-when-atom
                          nth-0-cons
                          nth-add1
                          car-cons cdr-cons
                          nfix-when-natp
                          length
                          len-of-cons
                          len-when-atom
                          update-nth-array
                          nth-update-nth
                          len-update-nth
                          ;; field-map-key-lookup
                          max
                          (:t len)
                          resize-list-when-zp
                          (:rules-of-class :executable-counterpart :here))
                         ((make-list-ac)
                          (repeat)))))

      (local (in-theory (e/d
                         (plus-collect-consts
                          field-map-key-lookup-open
                          field-map-key-lookup-recur-open
                          rstobj-fix-idempotent-for-st-intfld
                          rstobj-fix-idempotent-for-st-natfld
                          ,@(cdr (assoc :theorems
                                        (cdr (assoc 'nonneg-tr-p
                                                    (table-alist 'rstobj::typed-records
                                                                 (w state))))))
                          ,@(cdr (assoc :theorems
                                        (cdr (assoc 'ubp8-tr-p
                                                    (table-alist 'rstobj::typed-records
                                                                 (w state)))))))
                         ((field-map-key-lookup-recur)))))


      (defstobj st$c
        (natarr0$c  :type (array (integer 0 *) (32))
                    :initially 0)
        (natarr1$c  :type (array (integer 0 *) (32))
                    :initially 0)
        (natarr2$c  :type (array (integer 0 *) (32))
                    :initially 0)
        (natarr3$c  :type (array (integer 0 *) (32))
                    :initially 0)
        (natarr4$c  :type (array (integer 0 *) (32))
                    :initially 0)
        (natarr5$c  :type (array (integer 0 *) (32))
                    :initially 0)
        (natarr6$c  :type (array (integer 0 *) (32))
                    :initially 0)
        (natarr7$c  :type (array (integer 0 *) (32))
                    :initially 0)


        (u8arr0$c   :type (array (unsigned-byte 8) (64))
                    :initially 0
                    :resizable t)
        (u8arr1$c   :type (array (unsigned-byte 8) (64))
                    :initially 0
                    :resizable t)
        (u8arr2$c   :type (array (unsigned-byte 8) (64))
                    :initially 0
                    :resizable t)
        (u8arr3$c   :type (array (unsigned-byte 8) (64))
                    :initially 0
                    :resizable t)
        (u8arr4$c   :type (array (unsigned-byte 8) (64))
                    :initially 0
                    :resizable t)
        (u8arr5$c   :type (array (unsigned-byte 8) (64))
                    :initially 0
                    :resizable t)
        (u8arr6$c   :type (array (unsigned-byte 8) (64))
                    :initially 0
                    :resizable t)
        (u8arr7$c   :type (array (unsigned-byte 8) (64))
                    :initially 0
                    :resizable t)

        (intfld0$c  :type integer
                    :initially 5)
        (intfld1$c  :type integer
                    :initially 5)
        (intfld2$c  :type integer
                    :initially 5)
        (intfld3$c  :type integer
                    :initially 5)
        (intfld4$c  :type integer
                    :initially 5)
        (intfld5$c  :type integer
                    :initially 5)
        (intfld6$c  :type integer
                    :initially 5)
        (intfld7$c  :type integer
                    :initially 5)

        (natfld0$c :type (integer 0 *)
                   :initially 0)
        (natfld1$c :type (integer 0 *)
                   :initially 0)
        (natfld2$c :type (integer 0 *)
                   :initially 0)
        (natfld3$c :type (integer 0 *)
                   :initially 0)
        (natfld4$c :type (integer 0 *)
                   :initially 0)
        (natfld5$c :type (integer 0 *)
                   :initially 0)
        (natfld6$c :type (integer 0 *)
                   :initially 0)
        (natfld7$c :type (integer 0 *)
                   :initially 0))


      (defun empty-u8arr0$c (st$c)
        (declare (xargs :stobjs st$c))
        (resize-u8arr0$c 0 st$c))

      (defun empty-u8arr1$c (st$c)
        (declare (xargs :stobjs st$c))
        (resize-u8arr1$c 0 st$c))

      (defun empty-u8arr2$c (st$c)
        (declare (xargs :stobjs st$c))
        (resize-u8arr2$c 0 st$c))

      (defun empty-u8arr3$c (st$c)
        (declare (xargs :stobjs st$c))
        (resize-u8arr3$c 0 st$c))

      (defun empty-u8arr4$c (st$c)
        (declare (xargs :stobjs st$c))
        (resize-u8arr4$c 0 st$c))

      (defun empty-u8arr5$c (st$c)
        (declare (xargs :stobjs st$c))
        (resize-u8arr5$c 0 st$c))

      (defun empty-u8arr6$c (st$c)
        (declare (xargs :stobjs st$c))
        (resize-u8arr6$c 0 st$c))

      (defun empty-u8arr7$c (st$c)
        (declare (xargs :stobjs st$c))
        (resize-u8arr7$c 0 st$c))


      (defun stp$a (st$a)
        (declare (xargs :guard t)
                 (ignorable st$a))
        t)

      (defun create-st$a ()
        (declare (xargS :guard t))
        (let* ((st$a nil)
               (st$a (s :natarr0 nil st$a))
               (st$a (s :natarr1 nil st$a))
               (st$a (s :natarr2 nil st$a))
               (st$a (s :natarr3 nil st$a))
               (st$a (s :natarr4 nil st$a))
               (st$a (s :natarr5 nil st$a))
               (st$a (s :natarr6 nil st$a))
               (st$a (s :natarr7 nil st$a))
               (st$a (s :natarr0-length 32 st$a))
               (st$a (s :natarr1-length 32 st$a))
               (st$a (s :natarr2-length 32 st$a))
               (st$a (s :natarr3-length 32 st$a))
               (st$a (s :natarr4-length 32 st$a))
               (st$a (s :natarr5-length 32 st$a))
               (st$a (s :natarr6-length 32 st$a))
               (st$a (s :natarr7-length 32 st$a))
               (st$a (s :u8arr0 nil st$a))
               (st$a (s :u8arr1 nil st$a))
               (st$a (s :u8arr2 nil st$a))
               (st$a (s :u8arr3 nil st$a))
               (st$a (s :u8arr4 nil st$a))
               (st$a (s :u8arr5 nil st$a))
               (st$a (s :u8arr6 nil st$a))
               (st$a (s :u8arr7 nil st$a))
               (st$a (s :u8arr0-length 64 st$a))
               (st$a (s :u8arr1-length 64 st$a))
               (st$a (s :u8arr2-length 64 st$a))
               (st$a (s :u8arr3-length 64 st$a))
               (st$a (s :u8arr4-length 64 st$a))
               (st$a (s :u8arr5-length 64 st$a))
               (st$a (s :u8arr6-length 64 st$a))
               (st$a (s :u8arr7-length 64 st$a))
               (st$a (s :intfld0 5 st$a))
               (st$a (s :intfld1 5 st$a))
               (st$a (s :intfld2 5 st$a))
               (st$a (s :intfld3 5 st$a))
               (st$a (s :intfld4 5 st$a))
               (st$a (s :intfld5 5 st$a))
               (st$a (s :intfld6 5 st$a))
               (st$a (s :intfld7 5 st$a))
               (st$a (s :natfld0 0 st$a))
               (st$a (s :natfld1 0 st$a))
               (st$a (s :natfld2 0 st$a))
               (st$a (s :natfld3 0 st$a))
               (st$a (s :natfld4 0 st$a))
               (st$a (s :natfld5 0 st$a))
               (st$a (s :natfld6 0 st$a))
               (st$a (s :natfld7 0 st$a)))
          st$a))

      (defun natarr0-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :natarr0-length st$a)))

      (defun get-natarr0$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr0-length$a st$a)))))
        (nonneg-tr-get i (g :natarr0 st$a)))

      (defun set-natarr0$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr0-length$a st$a))
                                    (natp v))))
        (let* ((tr (g :natarr0 st$a))
               (tr (nonneg-tr-set i v tr)))
          (s :natarr0 tr st$a)))

      (defun natarr1-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :natarr1-length st$a)))

      (defun get-natarr1$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr1-length$a st$a)))))
        (nonneg-tr-get i (g :natarr1 st$a)))

      (defun set-natarr1$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr1-length$a st$a))
                                    (natp v))))
        (let* ((tr (g :natarr1 st$a))
               (tr (nonneg-tr-set i v tr)))
          (s :natarr1 tr st$a)))


      (defun natarr2-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :natarr2-length st$a)))

      (defun get-natarr2$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr2-length$a st$a)))))
        (nonneg-tr-get i (g :natarr2 st$a)))

      (defun set-natarr2$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr2-length$a st$a))
                                    (natp v))))
        (let* ((tr (g :natarr2 st$a))
               (tr (nonneg-tr-set i v tr)))
          (s :natarr2 tr st$a)))


      (defun natarr3-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :natarr3-length st$a)))

      (defun get-natarr3$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr3-length$a st$a)))))
        (nonneg-tr-get i (g :natarr3 st$a)))

      (defun set-natarr3$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr3-length$a st$a))
                                    (natp v))))
        (let* ((tr (g :natarr3 st$a))
               (tr (nonneg-tr-set i v tr)))
          (s :natarr3 tr st$a)))


      (defun natarr4-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :natarr4-length st$a)))

      (defun get-natarr4$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr4-length$a st$a)))))
        (nonneg-tr-get i (g :natarr4 st$a)))

      (defun set-natarr4$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr4-length$a st$a))
                                    (natp v))))
        (let* ((tr (g :natarr4 st$a))
               (tr (nonneg-tr-set i v tr)))
          (s :natarr4 tr st$a)))


      (defun natarr5-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :natarr5-length st$a)))

      (defun get-natarr5$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr5-length$a st$a)))))
        (nonneg-tr-get i (g :natarr5 st$a)))

      (defun set-natarr5$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr5-length$a st$a))
                                    (natp v))))
        (let* ((tr (g :natarr5 st$a))
               (tr (nonneg-tr-set i v tr)))
          (s :natarr5 tr st$a)))


      (defun natarr6-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :natarr6-length st$a)))

      (defun get-natarr6$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr6-length$a st$a)))))
        (nonneg-tr-get i (g :natarr6 st$a)))

      (defun set-natarr6$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr6-length$a st$a))
                                    (natp v))))
        (let* ((tr (g :natarr6 st$a))
               (tr (nonneg-tr-set i v tr)))
          (s :natarr6 tr st$a)))


      (defun natarr7-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :natarr7-length st$a)))

      (defun get-natarr7$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr7-length$a st$a)))))
        (nonneg-tr-get i (g :natarr7 st$a)))

      (defun set-natarr7$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (natarr7-length$a st$a))
                                    (natp v))))
        (let* ((tr (g :natarr7 st$a))
               (tr (nonneg-tr-set i v tr)))
          (s :natarr7 tr st$a)))




      (defun u8arr0-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :u8arr0-length st$a)))

      (defun get-u8arr0$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr0-length$a st$a)))))
        (ubp8-tr-get i (g :u8arr0 st$a)))

      (defun set-u8arr0$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr0-length$a st$a))
                                    (unsigned-byte-p 8 v))))
        (let* ((tr (g :u8arr0 st$a))
               (tr (ubp8-tr-set i v tr)))
          (s :u8arr0 tr st$a)))

      (defun resize-u8arr0$a (n st$a)
        (declare (xargs :guard (and (natp n)
                                    (<= (u8arr0-length$a st$a) n))))
        (s :u8arr0-length n st$a))

      (defun empty-u8arr0$a (st$a)
        (declare (xargs :guard t))
        (let* ((st$a (s :u8arr0-length 0 st$a)))
          (s :u8arr0 nil st$a)))



      (defun u8arr1-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :u8arr1-length st$a)))

      (defun get-u8arr1$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr1-length$a st$a)))))
        (ubp8-tr-get i (g :u8arr1 st$a)))

      (defun set-u8arr1$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr1-length$a st$a))
                                    (unsigned-byte-p 8 v))))
        (let* ((tr (g :u8arr1 st$a))
               (tr (ubp8-tr-set i v tr)))
          (s :u8arr1 tr st$a)))

      (defun resize-u8arr1$a (n st$a)
        (declare (xargs :guard (and (natp n)
                                    (<= (u8arr1-length$a st$a) n))))
        (s :u8arr1-length n st$a))

      (defun empty-u8arr1$a (st$a)
        (declare (xargs :guard t))
        (let* ((st$a (s :u8arr1-length 0 st$a)))
          (s :u8arr1 nil st$a)))



      (defun u8arr2-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :u8arr2-length st$a)))

      (defun get-u8arr2$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr2-length$a st$a)))))
        (ubp8-tr-get i (g :u8arr2 st$a)))

      (defun set-u8arr2$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr2-length$a st$a))
                                    (unsigned-byte-p 8 v))))
        (let* ((tr (g :u8arr2 st$a))
               (tr (ubp8-tr-set i v tr)))
          (s :u8arr2 tr st$a)))

      (defun resize-u8arr2$a (n st$a)
        (declare (xargs :guard (and (natp n)
                                    (<= (u8arr2-length$a st$a) n))))
        (s :u8arr2-length n st$a))

      (defun empty-u8arr2$a (st$a)
        (declare (xargs :guard t))
        (let* ((st$a (s :u8arr2-length 0 st$a)))
          (s :u8arr2 nil st$a)))



      (defun u8arr3-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :u8arr3-length st$a)))

      (defun get-u8arr3$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr3-length$a st$a)))))
        (ubp8-tr-get i (g :u8arr3 st$a)))

      (defun set-u8arr3$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr3-length$a st$a))
                                    (unsigned-byte-p 8 v))))
        (let* ((tr (g :u8arr3 st$a))
               (tr (ubp8-tr-set i v tr)))
          (s :u8arr3 tr st$a)))

      (defun resize-u8arr3$a (n st$a)
        (declare (xargs :guard (and (natp n)
                                    (<= (u8arr3-length$a st$a) n))))
        (s :u8arr3-length n st$a))

      (defun empty-u8arr3$a (st$a)
        (declare (xargs :guard t))
        (let* ((st$a (s :u8arr3-length 0 st$a)))
          (s :u8arr3 nil st$a)))



      (defun u8arr4-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :u8arr4-length st$a)))

      (defun get-u8arr4$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr4-length$a st$a)))))
        (ubp8-tr-get i (g :u8arr4 st$a)))

      (defun set-u8arr4$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr4-length$a st$a))
                                    (unsigned-byte-p 8 v))))
        (let* ((tr (g :u8arr4 st$a))
               (tr (ubp8-tr-set i v tr)))
          (s :u8arr4 tr st$a)))

      (defun resize-u8arr4$a (n st$a)
        (declare (xargs :guard (and (natp n)
                                    (<= (u8arr4-length$a st$a) n))))
        (s :u8arr4-length n st$a))

      (defun empty-u8arr4$a (st$a)
        (declare (xargs :guard t))
        (let* ((st$a (s :u8arr4-length 0 st$a)))
          (s :u8arr4 nil st$a)))



      (defun u8arr5-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :u8arr5-length st$a)))

      (defun get-u8arr5$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr5-length$a st$a)))))
        (ubp8-tr-get i (g :u8arr5 st$a)))

      (defun set-u8arr5$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr5-length$a st$a))
                                    (unsigned-byte-p 8 v))))
        (let* ((tr (g :u8arr5 st$a))
               (tr (ubp8-tr-set i v tr)))
          (s :u8arr5 tr st$a)))

      (defun resize-u8arr5$a (n st$a)
        (declare (xargs :guard (and (natp n)
                                    (<= (u8arr5-length$a st$a) n))))
        (s :u8arr5-length n st$a))

      (defun empty-u8arr5$a (st$a)
        (declare (xargs :guard t))
        (let* ((st$a (s :u8arr5-length 0 st$a)))
          (s :u8arr5 nil st$a)))



      (defun u8arr6-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :u8arr6-length st$a)))

      (defun get-u8arr6$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr6-length$a st$a)))))
        (ubp8-tr-get i (g :u8arr6 st$a)))

      (defun set-u8arr6$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr6-length$a st$a))
                                    (unsigned-byte-p 8 v))))
        (let* ((tr (g :u8arr6 st$a))
               (tr (ubp8-tr-set i v tr)))
          (s :u8arr6 tr st$a)))

      (defun resize-u8arr6$a (n st$a)
        (declare (xargs :guard (and (natp n)
                                    (<= (u8arr6-length$a st$a) n))))
        (s :u8arr6-length n st$a))

      (defun empty-u8arr6$a (st$a)
        (declare (xargs :guard t))
        (let* ((st$a (s :u8arr6-length 0 st$a)))
          (s :u8arr6 nil st$a)))



      (defun u8arr7-length$a (st$a)
        (declare (xargs :guard t))
        (nfix (g :u8arr7-length st$a)))

      (defun get-u8arr7$a (i st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr7-length$a st$a)))))
        (ubp8-tr-get i (g :u8arr7 st$a)))

      (defun set-u8arr7$a (i v st$a)
        (declare (xargs :guard (and (natp i)
                                    (< i (u8arr7-length$a st$a))
                                    (unsigned-byte-p 8 v))))
        (let* ((tr (g :u8arr7 st$a))
               (tr (ubp8-tr-set i v tr)))
          (s :u8arr7 tr st$a)))

      (defun resize-u8arr7$a (n st$a)
        (declare (xargs :guard (and (natp n)
                                    (<= (u8arr7-length$a st$a) n))))
        (s :u8arr7-length n st$a))

      (defun empty-u8arr7$a (st$a)
        (declare (xargs :guard t))
        (let* ((st$a (s :u8arr7-length 0 st$a)))
          (s :u8arr7 nil st$a)))



      (defun get-intfld0$a (st$a)
        (declare (xargs :guard t))
        (ifix (g :intfld0 st$a)))

      (defun set-intfld0$a (v st$a)
        (declare (xargs :guard (integerp v)))
        (s :intfld0 v st$a))

      (defun get-natfld0$a (st$a)
        (declare (xargs :guard t))
        (nonneg-fix (g :natfld0 st$a)))

      (defun set-natfld0$a (v st$a)
        (declare (xargs :guard (natp v)))
        (s :natfld0 v st$a))



      (defun get-intfld1$a (st$a)
        (declare (xargs :guard t))
        (ifix (g :intfld1 st$a)))

      (defun set-intfld1$a (v st$a)
        (declare (xargs :guard (integerp v)))
        (s :intfld1 v st$a))

      (defun get-natfld1$a (st$a)
        (declare (xargs :guard t))
        (nonneg-fix (g :natfld1 st$a)))

      (defun set-natfld1$a (v st$a)
        (declare (xargs :guard (natp v)))
        (s :natfld1 v st$a))



      (defun get-intfld2$a (st$a)
        (declare (xargs :guard t))
        (ifix (g :intfld2 st$a)))

      (defun set-intfld2$a (v st$a)
        (declare (xargs :guard (integerp v)))
        (s :intfld2 v st$a))

      (defun get-natfld2$a (st$a)
        (declare (xargs :guard t))
        (nonneg-fix (g :natfld2 st$a)))

      (defun set-natfld2$a (v st$a)
        (declare (xargs :guard (natp v)))
        (s :natfld2 v st$a))



      (defun get-intfld3$a (st$a)
        (declare (xargs :guard t))
        (ifix (g :intfld3 st$a)))

      (defun set-intfld3$a (v st$a)
        (declare (xargs :guard (integerp v)))
        (s :intfld3 v st$a))

      (defun get-natfld3$a (st$a)
        (declare (xargs :guard t))
        (nonneg-fix (g :natfld3 st$a)))

      (defun set-natfld3$a (v st$a)
        (declare (xargs :guard (natp v)))
        (s :natfld3 v st$a))



      (defun get-intfld4$a (st$a)
        (declare (xargs :guard t))
        (ifix (g :intfld4 st$a)))

      (defun set-intfld4$a (v st$a)
        (declare (xargs :guard (integerp v)))
        (s :intfld4 v st$a))

      (defun get-natfld4$a (st$a)
        (declare (xargs :guard t))
        (nonneg-fix (g :natfld4 st$a)))

      (defun set-natfld4$a (v st$a)
        (declare (xargs :guard (natp v)))
        (s :natfld4 v st$a))



      (defun get-intfld5$a (st$a)
        (declare (xargs :guard t))
        (ifix (g :intfld5 st$a)))

      (defun set-intfld5$a (v st$a)
        (declare (xargs :guard (integerp v)))
        (s :intfld5 v st$a))

      (defun get-natfld5$a (st$a)
        (declare (xargs :guard t))
        (nonneg-fix (g :natfld5 st$a)))

      (defun set-natfld5$a (v st$a)
        (declare (xargs :guard (natp v)))
        (s :natfld5 v st$a))



      (defun get-intfld6$a (st$a)
        (declare (xargs :guard t))
        (ifix (g :intfld6 st$a)))

      (defun set-intfld6$a (v st$a)
        (declare (xargs :guard (integerp v)))
        (s :intfld6 v st$a))

      (defun get-natfld6$a (st$a)
        (declare (xargs :guard t))
        (nonneg-fix (g :natfld6 st$a)))

      (defun set-natfld6$a (v st$a)
        (declare (xargs :guard (natp v)))
        (s :natfld6 v st$a))



      (defun get-intfld7$a (st$a)
        (declare (xargs :guard t))
        (ifix (g :intfld7 st$a)))

      (defun set-intfld7$a (v st$a)
        (declare (xargs :guard (integerp v)))
        (s :intfld7 v st$a))

      (defun get-natfld7$a (st$a)
        (declare (xargs :guard t))
        (nonneg-fix (g :natfld7 st$a)))

      (defun set-natfld7$a (v st$a)
        (declare (xargs :guard (natp v)))
        (s :natfld7 v st$a))





      (local
       (progn

         (defconst *rstobj-tmp-field-map*
           (list (make-array-fieldinfo :tr-key :natarr0 :size-key :natarr0-length)
                 (make-array-fieldinfo :tr-key :natarr1 :size-key :natarr1-length)
                 (make-array-fieldinfo :tr-key :natarr2 :size-key :natarr2-length)
                 (make-array-fieldinfo :tr-key :natarr3 :size-key :natarr3-length)
                 (make-array-fieldinfo :tr-key :natarr4 :size-key :natarr4-length)
                 (make-array-fieldinfo :tr-key :natarr5 :size-key :natarr5-length)
                 (make-array-fieldinfo :tr-key :natarr6 :size-key :natarr6-length)
                 (make-array-fieldinfo :tr-key :natarr7 :size-key :natarr7-length)
                 (make-array-fieldinfo :tr-key :u8arr0 :size-key :u8arr0-length)
                 (make-array-fieldinfo :tr-key :u8arr1 :size-key :u8arr1-length)
                 (make-array-fieldinfo :tr-key :u8arr2 :size-key :u8arr2-length)
                 (make-array-fieldinfo :tr-key :u8arr3 :size-key :u8arr3-length)
                 (make-array-fieldinfo :tr-key :u8arr4 :size-key :u8arr4-length)
                 (make-array-fieldinfo :tr-key :u8arr5 :size-key :u8arr5-length)
                 (make-array-fieldinfo :tr-key :u8arr6 :size-key :u8arr6-length)
                 (make-array-fieldinfo :tr-key :u8arr7 :size-key :u8arr7-length)
                 (make-scalar-fieldinfo :key :intfld0)
                 (make-scalar-fieldinfo :key :intfld1)
                 (make-scalar-fieldinfo :key :intfld2)
                 (make-scalar-fieldinfo :key :intfld3)
                 (make-scalar-fieldinfo :key :intfld4)
                 (make-scalar-fieldinfo :key :intfld5)
                 (make-scalar-fieldinfo :key :intfld6)
                 (make-scalar-fieldinfo :key :intfld7)
                 (make-scalar-fieldinfo :key :natfld0)
                 (make-scalar-fieldinfo :key :natfld1)
                 (make-scalar-fieldinfo :key :natfld2)
                 (make-scalar-fieldinfo :key :natfld3)
                 (make-scalar-fieldinfo :key :natfld4)
                 (make-scalar-fieldinfo :key :natfld5)
                 (make-scalar-fieldinfo :key :natfld6)
                 (make-scalar-fieldinfo :key :natfld7)
                 ))

         (defund rstobj-tmp-field-map () *rstobj-tmp-field-map*)

         (defun rstobj-tmp-tr-get (name i tr)
           (case name
             (:natarr0 (nonneg-tr-get i tr))
             (:natarr1 (nonneg-tr-get i tr))
             (:natarr2 (nonneg-tr-get i tr))
             (:natarr3 (nonneg-tr-get i tr))
             (:natarr4 (nonneg-tr-get i tr))
             (:natarr5 (nonneg-tr-get i tr))
             (:natarr6 (nonneg-tr-get i tr))
             (:natarr7 (nonneg-tr-get i tr))
             (:u8arr0 (ubp8-tr-get i tr))
             (:u8arr1 (ubp8-tr-get i tr))
             (:u8arr2 (ubp8-tr-get i tr))
             (:u8arr3 (ubp8-tr-get i tr))
             (:u8arr4 (ubp8-tr-get i tr))
             (:u8arr5 (ubp8-tr-get i tr))
             (:u8arr6 (ubp8-tr-get i tr))
             (:u8arr7 (ubp8-tr-get i tr))
             ))

         (defun rstobj-tmp-tr-set (name i v tr)
           (case name
             (:natarr0 (nonneg-tr-set i v tr))
             (:natarr1 (nonneg-tr-set i v tr))
             (:natarr2 (nonneg-tr-set i v tr))
             (:natarr3 (nonneg-tr-set i v tr))
             (:natarr4 (nonneg-tr-set i v tr))
             (:natarr5 (nonneg-tr-set i v tr))
             (:natarr6 (nonneg-tr-set i v tr))
             (:natarr7 (nonneg-tr-set i v tr))
             (:u8arr0 (ubp8-tr-set i v tr))
             (:u8arr1 (ubp8-tr-set i v tr))
             (:u8arr2 (ubp8-tr-set i v tr))
             (:u8arr3 (ubp8-tr-set i v tr))
             (:u8arr4 (ubp8-tr-set i v tr))
             (:u8arr5 (ubp8-tr-set i v tr))
             (:u8arr6 (ubp8-tr-set i v tr))
             (:u8arr7 (ubp8-tr-set i v tr))
             ))

         (defun rstobj-tmp-tr-fix (name v)
           (case name
             (:natarr0 (nonneg-fix v))
             (:natarr1 (nonneg-fix v))
             (:natarr2 (nonneg-fix v))
             (:natarr3 (nonneg-fix v))
             (:natarr4 (nonneg-fix v))
             (:natarr5 (nonneg-fix v))
             (:natarr6 (nonneg-fix v))
             (:natarr7 (nonneg-fix v))
             (:u8arr0 (ubp-fix 8 v))
             (:u8arr1 (ubp-fix 8 v))
             (:u8arr2 (ubp-fix 8 v))
             (:u8arr3 (ubp-fix 8 v))
             (:u8arr4 (ubp-fix 8 v))
             (:u8arr5 (ubp-fix 8 v))
             (:u8arr6 (ubp-fix 8 v))
             (:u8arr7 (ubp-fix 8 v))
             ))

         (defun rstobj-tmp-tr-default (name)
           (case name
             (:natarr0 0)
             (:natarr1 0)
             (:natarr2 0)
             (:natarr3 0)
             (:natarr4 0)
             (:natarr5 0)
             (:natarr6 0)
             (:natarr7 0)
             (:u8arr0 0)
             (:u8arr1 0)
             (:u8arr2 0)
             (:u8arr3 0)
             (:u8arr4 0)
             (:u8arr5 0)
             (:u8arr6 0)
             (:u8arr7 0)
             ))


         (defun rstobj-tmp-tr-elem-p (name v)
           (case name
             (:natarr0 (natp v))
             (:natarr1 (natp v))
             (:natarr2 (natp v))
             (:natarr3 (natp v))
             (:natarr4 (natp v))
             (:natarr5 (natp v))
             (:natarr6 (natp v))
             (:natarr7 (natp v))
             (:u8arr0 (unsigned-byte-p 8 v))
             (:u8arr1 (unsigned-byte-p 8 v))
             (:u8arr2 (unsigned-byte-p 8 v))
             (:u8arr3 (unsigned-byte-p 8 v))
             (:u8arr4 (unsigned-byte-p 8 v))
             (:u8arr5 (unsigned-byte-p 8 v))
             (:u8arr6 (unsigned-byte-p 8 v))
             (:u8arr7 (unsigned-byte-p 8 v))
             ))

         (defun rstobj-tmp-scalar-fix (name v)
           (case name
             (:intfld0 (ifix v))
             (:intfld1 (ifix v))
             (:intfld2 (ifix v))
             (:intfld3 (ifix v))
             (:intfld4 (ifix v))
             (:intfld5 (ifix v))
             (:intfld6 (ifix v))
             (:intfld7 (ifix v))
             (:natfld0 (nonneg-fix v))
             (:natfld1 (nonneg-fix v))
             (:natfld2 (nonneg-fix v))
             (:natfld3 (nonneg-fix v))
             (:natfld4 (nonneg-fix v))
             (:natfld5 (nonneg-fix v))
             (:natfld6 (nonneg-fix v))
             (:natfld7 (nonneg-fix v))
             ))

         (defun rstobj-tmp-scalar-elem-p (name v)
           (case name
             (:intfld0 (integerp v))
             (:intfld1 (integerp v))
             (:intfld2 (integerp v))
             (:intfld3 (integerp v))
             (:intfld4 (integerp v))
             (:intfld5 (integerp v))
             (:intfld6 (integerp v))
             (:intfld7 (integerp v))
             (:natfld0 (natp v))
             (:natfld1 (natp v))
             (:natfld2 (natp v))
             (:natfld3 (natp v))
             (:natfld4 (natp v))
             (:natfld5 (natp v))
             (:natfld6 (natp v))
             (:natfld7 (natp v))
             ))

         (defun-sk rstobj-tmp-field-corr (st$c st$a)
           (forall (idx i)
                   (let ((entry (nth idx (rstobj-tmp-field-map))))
                     (and (implies (equal (acl2::tag entry) :array)
                                   ;; array
                                   (b* (((array-fieldinfo x) entry)
                                        (arr (nth idx st$c))
                                        (tr  (g x.tr-key st$a)))
                                     (and (implies (natp i)
                                                   (equal (rstobj-tmp-tr-get x.tr-key i tr)
                                                          (if (< i (len arr))
                                                              (nth i arr)
                                                            (rstobj-tmp-tr-default x.tr-key))))
                                          (equal (g x.size-key st$a)
                                                 (len arr)))))
                          (implies (equal (acl2::tag entry) :scalar)
                                   (b* (((scalar-fieldinfo x) entry))
                                     (equal (g x.key st$a)
                                            (nth idx st$c)))))))
           :rewrite :direct)

         (in-theory (disable rstobj-tmp-field-corr rstobj-tmp-field-corr-necc))


         (defthm rstobj-tmp-field-corr-of-size-key
           (mv-let (keytype idx)
             (field-map-key-lookup szkey (rstobj-tmp-field-map))
             (implies (and (rstobj-tmp-field-corr st$c st$a)
                           (equal keytype :size))
                      (equal (g szkey st$a)
                             (len (nth idx st$c)))))
           :hints (("goal" :by (:instance
                                (:functional-instance
                                 rstobj-field-corr-of-size-key
                                 (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
                                 (rstobj-field-corr rstobj-tmp-field-corr)
                                 (rstobj-field-map rstobj-tmp-field-map)
                                 (rstobj-tr-get rstobj-tmp-tr-get)
                                 (rstobj-tr-set rstobj-tmp-tr-set)
                                 (rstobj-tr-fix rstobj-tmp-tr-fix)
                                 (rstobj-tr-default rstobj-tmp-tr-default)
                                 (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
                                 (rstobj-scalar-fix rstobj-tmp-scalar-fix)
                                 (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
                                (rstobj$c st$c)
                                (rstobj$a st$a))
                    :in-theory (disable (rstobj-tmp-field-map))
                    :do-not-induct t)
                   (let ((lit (car clause)))
                     (case-match lit
                       ((f ('rstobj-tmp-field-corr . &) . &)
                        `(:in-theory (e/d ,(if (eq f 'equal)
                                               '(rstobj-tmp-field-corr)
                                             '(rstobj-tmp-field-corr-necc))
                                          ((rstobj-tmp-field-map)
                                           rstobj-tmp-tr-get
                                           rstobj-tmp-tr-fix
                                           rstobj-tmp-scalar-fix))))
                       (& '(:in-theory (enable (rstobj-tmp-field-map))))))))

         (defthm rstobj-tmp-field-corr-of-scalar-key
           (mv-let (keytype idx)
             (field-map-key-lookup sckey (rstobj-tmp-field-map))
             (implies (and (rstobj-tmp-field-corr st$c st$a)
                           (equal keytype :scalar))
                      (equal (g sckey st$a)
                             (nth idx st$c))))
           :hints (("goal" :by (:instance
                                (:functional-instance
                                 rstobj-field-corr-of-scalar-key
                                 (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
                                 (rstobj-field-corr rstobj-tmp-field-corr)
                                 (rstobj-field-map rstobj-tmp-field-map)
                                 (rstobj-tr-get rstobj-tmp-tr-get)
                                 (rstobj-tr-set rstobj-tmp-tr-set)
                                 (rstobj-tr-fix rstobj-tmp-tr-fix)
                                 (rstobj-tr-default rstobj-tmp-tr-default)
                                 (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
                                 (rstobj-scalar-fix rstobj-tmp-scalar-fix)
                                 (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
                                (rstobj$c st$c)
                                (rstobj$a st$a))
                    :do-not-induct t)))

         (defthm rstobj-tmp-field-corr-of-tr-key
           (mv-let (keytype idx)
             (field-map-key-lookup trkey (rstobj-tmp-field-map))
             (implies (and (rstobj-tmp-field-corr st$c st$a)
                           (equal keytype :array)
                           (natp i))
                      (equal (rstobj-tmp-tr-get trkey i (g trkey st$a))
                             (if (< i (len (nth idx st$c)))
                                 (nth i (nth idx st$c))
                               (rstobj-tmp-tr-default trkey)))))
           :hints (("goal" :by (:instance
                                (:functional-instance
                                 rstobj-field-corr-of-tr-key
                                 (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
                                 (rstobj-field-corr rstobj-tmp-field-corr)
                                 (rstobj-field-map rstobj-tmp-field-map)
                                 (rstobj-tr-get rstobj-tmp-tr-get)
                                 (rstobj-tr-set rstobj-tmp-tr-set)
                                 (rstobj-tr-fix rstobj-tmp-tr-fix)
                                 (rstobj-tr-default rstobj-tmp-tr-default)
                                 (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
                                 (rstobj-scalar-fix rstobj-tmp-scalar-fix)
                                 (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
                                (rstobj$c st$c)
                                (rstobj$a st$a))
                    :do-not-induct t)))


         (defthm rstobj-tmp-field-corr-of-tr-key-elaborate
           (mv-let (keytype idx)
             (field-map-key-lookup trkey (rstobj-tmp-field-map))
             (implies (and (rstobj-tmp-field-corr st$c st$a)
                           (equal keytype :array)
                           (natp i))
                      (and (implies (equal trkey :natarr0)
                                    (equal (nonneg-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :natarr1)
                                    (equal (nonneg-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :natarr2)
                                    (equal (nonneg-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :natarr3)
                                    (equal (nonneg-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :natarr4)
                                    (equal (nonneg-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :natarr5)
                                    (equal (nonneg-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :natarr6)
                                    (equal (nonneg-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :natarr7)
                                    (equal (nonneg-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :u8arr0)
                                    (equal (ubp8-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :u8arr1)
                                    (equal (ubp8-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :u8arr2)
                                    (equal (ubp8-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :u8arr3)
                                    (equal (ubp8-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :u8arr4)
                                    (equal (ubp8-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :u8arr5)
                                    (equal (ubp8-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :u8arr6)
                                    (equal (ubp8-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey))))
                           (implies (equal trkey :u8arr7)
                                    (equal (ubp8-tr-get i (g trkey st$a))
                                           (if (< i (len (nth idx st$c)))
                                               (nth i (nth idx st$c))
                                             (rstobj-tmp-tr-default trkey)))))))
           :hints (("goal" :use rstobj-tmp-field-corr-of-tr-key
                    :in-theory (e/d (rstobj-tmp-tr-get) (rstobj-tmp-field-corr-of-tr-key)))))


         (defthm rstobj-tmp-field-corr-of-update-scalar
           (implies (and (rstobj-tmp-field-corr st$c st$a)
                         (equal (acl2::tag (nth idx (rstobj-tmp-field-map))) :scalar)
                         (equal (scalar-fieldinfo->key (nth idx (rstobj-tmp-field-map))) key)
                         (equal v (rstobj-tmp-scalar-fix key v)))
                    (rstobj-tmp-field-corr (update-nth idx v st$c)
                                           (s key v st$a)))
           :hints (("goal" :by (:instance
                                (:functional-instance
                                 rstobj-field-corr-of-update-scalar
                                 (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
                                 (rstobj-field-corr rstobj-tmp-field-corr)
                                 (rstobj-field-map rstobj-tmp-field-map)
                                 (rstobj-tr-get rstobj-tmp-tr-get)
                                 (rstobj-tr-set rstobj-tmp-tr-set)
                                 (rstobj-tr-fix rstobj-tmp-tr-fix)
                                 (rstobj-tr-default rstobj-tmp-tr-default)
                                 (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
                                 (rstobj-scalar-fix rstobj-tmp-scalar-fix)
                                 (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
                                (rstobj$c st$c)
                                (rstobj$a st$a))
                    :do-not-induct t)))




         (defthm rstobj-tmp-field-corr-of-update-array
           (implies (and (rstobj-tmp-field-corr st$c st$a)
                         (equal (acl2::tag (nth idx (rstobj-tmp-field-map))) :array)
                         (equal (array-fieldinfo->tr-key (nth idx (rstobj-tmp-field-map))) key)
                         (equal tr1 (rstobj-tmp-tr-set key i v (g key st$a)))
                         (equal v (rstobj-tmp-tr-fix key v))
                         (natp i)
                         (< i (len (nth idx st$c))))
                    (rstobj-tmp-field-corr (update-nth idx (update-nth i v (nth idx st$c))
                                                       st$c)
                                           (s key tr1 st$a)))
           :hints (("goal" :by (:instance
                                (:functional-instance
                                 rstobj-field-corr-of-update-array
                                 (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
                                 (rstobj-field-corr rstobj-tmp-field-corr)
                                 (rstobj-field-map rstobj-tmp-field-map)
                                 (rstobj-tr-get rstobj-tmp-tr-get)
                                 (rstobj-tr-set rstobj-tmp-tr-set)
                                 (rstobj-tr-fix rstobj-tmp-tr-fix)
                                 (rstobj-tr-default rstobj-tmp-tr-default)
                                 (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
                                 (rstobj-scalar-fix rstobj-tmp-scalar-fix)
                                 (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
                                (rstobj$c st$c)
                                (rstobj$a st$a))
                    :do-not-induct t)))


         (defthm rstobj-tmp-field-corr-of-grow-array
           (implies (and (rstobj-tmp-field-corr st$c st$a)
                         (equal (acl2::tag (nth idx (rstobj-tmp-field-map))) :array)
                         (equal (array-fieldinfo->size-key (nth idx (rstobj-tmp-field-map))) size-key)
                         (natp new-size)
                         (<= (len (nth idx st$c)) new-size)
                         (equal default (rstobj-tmp-tr-default
                                         (array-fieldinfo->tr-key (nth idx (rstobj-tmp-field-map))))))
                    (rstobj-tmp-field-corr (update-nth idx
                                                       (resize-list (nth idx st$c) new-size default)
                                                       st$c)
                                           (s size-key new-size st$a)))
           :hints (("goal" :by (:instance
                                (:functional-instance
                                 rstobj-field-corr-of-grow-array
                                 (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
                                 (rstobj-field-corr rstobj-tmp-field-corr)
                                 (rstobj-field-map rstobj-tmp-field-map)
                                 (rstobj-tr-get rstobj-tmp-tr-get)
                                 (rstobj-tr-set rstobj-tmp-tr-set)
                                 (rstobj-tr-fix rstobj-tmp-tr-fix)
                                 (rstobj-tr-default rstobj-tmp-tr-default)
                                 (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
                                 (rstobj-scalar-fix rstobj-tmp-scalar-fix)
                                 (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
                                (rstobj$c st$c)
                                (rstobj$a st$a))
                    :do-not-induct t)))

         (defthm rstobj-tmp-field-corr-of-empty-array
           (implies (and (rstobj-tmp-field-corr st$c st$a)
                         (equal (acl2::tag (nth idx (rstobj-tmp-field-map))) :array)
                         (equal (array-fieldinfo->tr-key (nth idx (rstobj-tmp-field-map))) tr-key)
                         (equal (array-fieldinfo->size-key (nth idx (rstobj-tmp-field-map))) size-key))
                    (rstobj-tmp-field-corr (update-nth idx nil st$c)
                                           (s tr-key nil (s size-key 0 st$a))))
           :hints (("goal" :by (:instance
                                (:functional-instance
                                 rstobj-field-corr-of-empty-array
                                 (rstobj-field-corr-witness rstobj-tmp-field-corr-witness)
                                 (rstobj-field-corr rstobj-tmp-field-corr)
                                 (rstobj-field-map rstobj-tmp-field-map)
                                 (rstobj-tr-get rstobj-tmp-tr-get)
                                 (rstobj-tr-set rstobj-tmp-tr-set)
                                 (rstobj-tr-fix rstobj-tmp-tr-fix)
                                 (rstobj-tr-default rstobj-tmp-tr-default)
                                 (rstobj-tr-elem-p rstobj-tmp-tr-elem-p)
                                 (rstobj-scalar-fix rstobj-tmp-scalar-fix)
                                 (rstobj-scalar-elem-p rstobj-tmp-scalar-elem-p))
                                (rstobj$c st$c)
                                (rstobj$a st$a))
                    :do-not-induct t)))


         (defthm rstobj-tmp-field-corr-of-create
           (rstobj-tmp-field-corr (create-st$c) (create-st$a))
           :hints(("Goal" :in-theory (e/d (rstobj-tmp-field-corr))
                   :expand ((:free (a b c) (nth a (cons b c)))))))


         (defun-nx rstobj-tmp-corr (st$c st$a)
           (and (st$cp st$c)
                (rstobj-tmp-field-corr st$c st$a)))

         (defthm field-lookup-in-rstobj-tmp-field-map
           (implies (syntaxp (quotep key))
                    (equal (field-map-key-lookup key (rstobj-tmp-field-map))
                           (field-map-key-lookup key *rstobj-tmp-field-map*))))

         (defthm index-lookup-in-rstobj-tmp-field-map
           (implies (syntaxp (quotep idx))
                    (equal (nth idx (rstobj-tmp-field-map))
                           (nth idx *rstobj-tmp-field-map*))))



         (defthm natarr0$cp-of-repeat
           (implies (natp v)
                    (natarr0$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat natarr0$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm natarr0$cp-of-update-nth
           (implies (and (natp v)
                         (natarr0$cp x)
                         (<= (nfix i) (len x)))
                    (natarr0$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable natarr0$cp update-nth len))))

         (defthm natarr0$cp-of-resize-list
           (implies (and (natp v)
                         (natarr0$cp x))
                    (natarr0$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))

         (defthm u8arr0$cp-of-repeat
           (implies (unsigned-byte-p 8 v)
                    (u8arr0$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat u8arr0$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm u8arr0$cp-of-update-nth
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr0$cp x)
                         (<= (nfix i) (len x)))
                    (u8arr0$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable u8arr0$cp update-nth len))))

         (defthm u8arr0$cp-of-resize-list
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr0$cp x))
                    (u8arr0$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))


         (defthm natarr1$cp-of-repeat
           (implies (natp v)
                    (natarr1$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat natarr1$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm natarr1$cp-of-update-nth
           (implies (and (natp v)
                         (natarr1$cp x)
                         (<= (nfix i) (len x)))
                    (natarr1$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable natarr1$cp update-nth len))))

         (defthm natarr1$cp-of-resize-list
           (implies (and (natp v)
                         (natarr1$cp x))
                    (natarr1$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))

         (defthm u8arr1$cp-of-repeat
           (implies (unsigned-byte-p 8 v)
                    (u8arr1$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat u8arr1$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm u8arr1$cp-of-update-nth
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr1$cp x)
                         (<= (nfix i) (len x)))
                    (u8arr1$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable u8arr1$cp update-nth len))))

         (defthm u8arr1$cp-of-resize-list
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr1$cp x))
                    (u8arr1$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))


         (defthm natarr2$cp-of-repeat
           (implies (natp v)
                    (natarr2$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat natarr2$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm natarr2$cp-of-update-nth
           (implies (and (natp v)
                         (natarr2$cp x)
                         (<= (nfix i) (len x)))
                    (natarr2$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable natarr2$cp update-nth len))))

         (defthm natarr2$cp-of-resize-list
           (implies (and (natp v)
                         (natarr2$cp x))
                    (natarr2$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))

         (defthm u8arr2$cp-of-repeat
           (implies (unsigned-byte-p 8 v)
                    (u8arr2$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat u8arr2$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm u8arr2$cp-of-update-nth
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr2$cp x)
                         (<= (nfix i) (len x)))
                    (u8arr2$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable u8arr2$cp update-nth len))))

         (defthm u8arr2$cp-of-resize-list
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr2$cp x))
                    (u8arr2$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))


         (defthm natarr3$cp-of-repeat
           (implies (natp v)
                    (natarr3$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat natarr3$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm natarr3$cp-of-update-nth
           (implies (and (natp v)
                         (natarr3$cp x)
                         (<= (nfix i) (len x)))
                    (natarr3$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable natarr3$cp update-nth len))))

         (defthm natarr3$cp-of-resize-list
           (implies (and (natp v)
                         (natarr3$cp x))
                    (natarr3$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))

         (defthm u8arr3$cp-of-repeat
           (implies (unsigned-byte-p 8 v)
                    (u8arr3$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat u8arr3$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm u8arr3$cp-of-update-nth
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr3$cp x)
                         (<= (nfix i) (len x)))
                    (u8arr3$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable u8arr3$cp update-nth len))))

         (defthm u8arr3$cp-of-resize-list
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr3$cp x))
                    (u8arr3$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))


         (defthm natarr4$cp-of-repeat
           (implies (natp v)
                    (natarr4$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat natarr4$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm natarr4$cp-of-update-nth
           (implies (and (natp v)
                         (natarr4$cp x)
                         (<= (nfix i) (len x)))
                    (natarr4$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable natarr4$cp update-nth len))))

         (defthm natarr4$cp-of-resize-list
           (implies (and (natp v)
                         (natarr4$cp x))
                    (natarr4$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))

         (defthm u8arr4$cp-of-repeat
           (implies (unsigned-byte-p 8 v)
                    (u8arr4$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat u8arr4$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm u8arr4$cp-of-update-nth
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr4$cp x)
                         (<= (nfix i) (len x)))
                    (u8arr4$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable u8arr4$cp update-nth len))))

         (defthm u8arr4$cp-of-resize-list
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr4$cp x))
                    (u8arr4$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))


         (defthm natarr5$cp-of-repeat
           (implies (natp v)
                    (natarr5$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat natarr5$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm natarr5$cp-of-update-nth
           (implies (and (natp v)
                         (natarr5$cp x)
                         (<= (nfix i) (len x)))
                    (natarr5$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable natarr5$cp update-nth len))))

         (defthm natarr5$cp-of-resize-list
           (implies (and (natp v)
                         (natarr5$cp x))
                    (natarr5$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))

         (defthm u8arr5$cp-of-repeat
           (implies (unsigned-byte-p 8 v)
                    (u8arr5$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat u8arr5$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm u8arr5$cp-of-update-nth
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr5$cp x)
                         (<= (nfix i) (len x)))
                    (u8arr5$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable u8arr5$cp update-nth len))))

         (defthm u8arr5$cp-of-resize-list
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr5$cp x))
                    (u8arr5$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))


         (defthm natarr6$cp-of-repeat
           (implies (natp v)
                    (natarr6$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat natarr6$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm natarr6$cp-of-update-nth
           (implies (and (natp v)
                         (natarr6$cp x)
                         (<= (nfix i) (len x)))
                    (natarr6$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable natarr6$cp update-nth len))))

         (defthm natarr6$cp-of-resize-list
           (implies (and (natp v)
                         (natarr6$cp x))
                    (natarr6$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))

         (defthm u8arr6$cp-of-repeat
           (implies (unsigned-byte-p 8 v)
                    (u8arr6$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat u8arr6$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm u8arr6$cp-of-update-nth
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr6$cp x)
                         (<= (nfix i) (len x)))
                    (u8arr6$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable u8arr6$cp update-nth len))))

         (defthm u8arr6$cp-of-resize-list
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr6$cp x))
                    (u8arr6$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))


         (defthm natarr7$cp-of-repeat
           (implies (natp v)
                    (natarr7$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat natarr7$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm natarr7$cp-of-update-nth
           (implies (and (natp v)
                         (natarr7$cp x)
                         (<= (nfix i) (len x)))
                    (natarr7$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable natarr7$cp update-nth len))))

         (defthm natarr7$cp-of-resize-list
           (implies (and (natp v)
                         (natarr7$cp x))
                    (natarr7$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))

         (defthm u8arr7$cp-of-repeat
           (implies (unsigned-byte-p 8 v)
                    (u8arr7$cp (acl2::repeat v n)))
           :hints(("Goal" :in-theory (enable acl2::repeat u8arr7$cp)
                   :induct (acl2::repeat 0 n))))

         (defthm u8arr7$cp-of-update-nth
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr7$cp x)
                         (<= (nfix i) (len x)))
                    (u8arr7$cp (update-nth i v x)))
           :hints(("Goal" :in-theory (enable u8arr7$cp update-nth len))))

         (defthm u8arr7$cp-of-resize-list
           (implies (and (unsigned-byte-p 8 v)
                         (u8arr7$cp x))
                    (u8arr7$cp (resize-list x n v)))
           :hints(("Goal" :in-theory (enable resize-list))))









         ;; (local (defthm nonneg-fix-when-natp
         ;;            (implies (natp x)
         ;;                     (equal (nonneg-fix x) x))))


         ;; (local (defthm ifix-when-integerp
         ;;          (implies (integerp x)
         ;;                   (equal (ifix x) x))))


         (set-default-hints
          '((and stable-under-simplificationp
                 '(:in-theory (enable create-st$a create-st$c st$cp)))))))


      (local (in-theory (disable
                         (rstobj-tmp-field-corr)
                         (rstobj-tmp-field-map)
                         st$cp
                         create-st$a
                         (create-st$a)
                         create-st$c
                         (create-st$c))))

      (acl2::defabsstobj-events st
        :concrete st$c
        :corr-fn rstobj-tmp-corr
        :creator (create-st :logic create-st$a :exec create-st$c)
        :recognizer (stp :logic stp$a :exec st$cp)
        :exports
        (
         (natarr0-length :logic natarr0-length$a :exec natarr0$c-length)
         (get-natarr0 :logic get-natarr0$a :exec natarr0$ci)
         (set-natarr0 :logic set-natarr0$a :exec update-natarr0$ci)

         (natarr1-length :logic natarr1-length$a :exec natarr1$c-length)
         (get-natarr1 :logic get-natarr1$a :exec natarr1$ci)
         (set-natarr1 :logic set-natarr1$a :exec update-natarr1$ci)

         (natarr2-length :logic natarr2-length$a :exec natarr2$c-length)
         (get-natarr2 :logic get-natarr2$a :exec natarr2$ci)
         (set-natarr2 :logic set-natarr2$a :exec update-natarr2$ci)

         (natarr3-length :logic natarr3-length$a :exec natarr3$c-length)
         (get-natarr3 :logic get-natarr3$a :exec natarr3$ci)
         (set-natarr3 :logic set-natarr3$a :exec update-natarr3$ci)

         (natarr4-length :logic natarr4-length$a :exec natarr4$c-length)
         (get-natarr4 :logic get-natarr4$a :exec natarr4$ci)
         (set-natarr4 :logic set-natarr4$a :exec update-natarr4$ci)

         (natarr5-length :logic natarr5-length$a :exec natarr5$c-length)
         (get-natarr5 :logic get-natarr5$a :exec natarr5$ci)
         (set-natarr5 :logic set-natarr5$a :exec update-natarr5$ci)

         (natarr6-length :logic natarr6-length$a :exec natarr6$c-length)
         (get-natarr6 :logic get-natarr6$a :exec natarr6$ci)
         (set-natarr6 :logic set-natarr6$a :exec update-natarr6$ci)

         (natarr7-length :logic natarr7-length$a :exec natarr7$c-length)
         (get-natarr7 :logic get-natarr7$a :exec natarr7$ci)
         (set-natarr7 :logic set-natarr7$a :exec update-natarr7$ci)


         (u8arr0-length :logic u8arr0-length$a :exec u8arr0$c-length)
         (get-u8arr0 :logic get-u8arr0$a :exec u8arr0$ci)
         (set-u8arr0 :logic set-u8arr0$a :exec update-u8arr0$ci)
         (resize-u8arr0 :logic resize-u8arr0$a :exec resize-u8arr0$c)
         (empty-u8arr0 :logic empty-u8arr0$a :exec empty-u8arr0$c)

         (u8arr1-length :logic u8arr1-length$a :exec u8arr1$c-length)
         (get-u8arr1 :logic get-u8arr1$a :exec u8arr1$ci)
         (set-u8arr1 :logic set-u8arr1$a :exec update-u8arr1$ci)
         (resize-u8arr1 :logic resize-u8arr1$a :exec resize-u8arr1$c)
         (empty-u8arr1 :logic empty-u8arr1$a :exec empty-u8arr1$c)

         (u8arr2-length :logic u8arr2-length$a :exec u8arr2$c-length)
         (get-u8arr2 :logic get-u8arr2$a :exec u8arr2$ci)
         (set-u8arr2 :logic set-u8arr2$a :exec update-u8arr2$ci)
         (resize-u8arr2 :logic resize-u8arr2$a :exec resize-u8arr2$c)
         (empty-u8arr2 :logic empty-u8arr2$a :exec empty-u8arr2$c)

         (u8arr3-length :logic u8arr3-length$a :exec u8arr3$c-length)
         (get-u8arr3 :logic get-u8arr3$a :exec u8arr3$ci)
         (set-u8arr3 :logic set-u8arr3$a :exec update-u8arr3$ci)
         (resize-u8arr3 :logic resize-u8arr3$a :exec resize-u8arr3$c)
         (empty-u8arr3 :logic empty-u8arr3$a :exec empty-u8arr3$c)

         (u8arr4-length :logic u8arr4-length$a :exec u8arr4$c-length)
         (get-u8arr4 :logic get-u8arr4$a :exec u8arr4$ci)
         (set-u8arr4 :logic set-u8arr4$a :exec update-u8arr4$ci)
         (resize-u8arr4 :logic resize-u8arr4$a :exec resize-u8arr4$c)
         (empty-u8arr4 :logic empty-u8arr4$a :exec empty-u8arr4$c)

         (u8arr5-length :logic u8arr5-length$a :exec u8arr5$c-length)
         (get-u8arr5 :logic get-u8arr5$a :exec u8arr5$ci)
         (set-u8arr5 :logic set-u8arr5$a :exec update-u8arr5$ci)
         (resize-u8arr5 :logic resize-u8arr5$a :exec resize-u8arr5$c)
         (empty-u8arr5 :logic empty-u8arr5$a :exec empty-u8arr5$c)

         (u8arr6-length :logic u8arr6-length$a :exec u8arr6$c-length)
         (get-u8arr6 :logic get-u8arr6$a :exec u8arr6$ci)
         (set-u8arr6 :logic set-u8arr6$a :exec update-u8arr6$ci)
         (resize-u8arr6 :logic resize-u8arr6$a :exec resize-u8arr6$c)
         (empty-u8arr6 :logic empty-u8arr6$a :exec empty-u8arr6$c)

         (u8arr7-length :logic u8arr7-length$a :exec u8arr7$c-length)
         (get-u8arr7 :logic get-u8arr7$a :exec u8arr7$ci)
         (set-u8arr7 :logic set-u8arr7$a :exec update-u8arr7$ci)
         (resize-u8arr7 :logic resize-u8arr7$a :exec resize-u8arr7$c)
         (empty-u8arr7 :logic empty-u8arr7$a :exec empty-u8arr7$c)

         (get-intfld0 :logic get-intfld0$a :exec intfld0$c)
         (set-intfld0 :logic set-intfld0$a :exec update-intfld0$c)

         (get-intfld1 :logic get-intfld1$a :exec intfld1$c)
         (set-intfld1 :logic set-intfld1$a :exec update-intfld1$c)

         (get-intfld2 :logic get-intfld2$a :exec intfld2$c)
         (set-intfld2 :logic set-intfld2$a :exec update-intfld2$c)

         (get-intfld3 :logic get-intfld3$a :exec intfld3$c)
         (set-intfld3 :logic set-intfld3$a :exec update-intfld3$c)

         (get-intfld4 :logic get-intfld4$a :exec intfld4$c)
         (set-intfld4 :logic set-intfld4$a :exec update-intfld4$c)

         (get-intfld5 :logic get-intfld5$a :exec intfld5$c)
         (set-intfld5 :logic set-intfld5$a :exec update-intfld5$c)

         (get-intfld6 :logic get-intfld6$a :exec intfld6$c)
         (set-intfld6 :logic set-intfld6$a :exec update-intfld6$c)

         (get-intfld7 :logic get-intfld7$a :exec intfld7$c)
         (set-intfld7 :logic set-intfld7$a :exec update-intfld7$c)

         (get-natfld0 :logic get-natfld0$a :exec natfld0$c)
         (set-natfld0 :logic set-natfld0$a :exec update-natfld0$c)

         (get-natfld1 :logic get-natfld1$a :exec natfld1$c)
         (set-natfld1 :logic set-natfld1$a :exec update-natfld1$c)

         (get-natfld2 :logic get-natfld2$a :exec natfld2$c)
         (set-natfld2 :logic set-natfld2$a :exec update-natfld2$c)

         (get-natfld3 :logic get-natfld3$a :exec natfld3$c)
         (set-natfld3 :logic set-natfld3$a :exec update-natfld3$c)

         (get-natfld4 :logic get-natfld4$a :exec natfld4$c)
         (set-natfld4 :logic set-natfld4$a :exec update-natfld4$c)

         (get-natfld5 :logic get-natfld5$a :exec natfld5$c)
         (set-natfld5 :logic set-natfld5$a :exec update-natfld5$c)

         (get-natfld6 :logic get-natfld6$a :exec natfld6$c)
         (set-natfld6 :logic set-natfld6$a :exec update-natfld6$c)

         (get-natfld7 :logic get-natfld7$a :exec natfld7$c)
         (set-natfld7 :logic set-natfld7$a :exec update-natfld7$c)

         )))))

