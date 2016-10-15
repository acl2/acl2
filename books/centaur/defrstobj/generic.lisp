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
; Generic theorems for abstract stobj correspondence
; Original author: Sol Swords <sswords@centtech.com>

(in-package "RSTOBJ")




(include-book "tools/rulesets" :dir :system)
(include-book "misc/records" :dir :system)
;; (include-book "clause-processors/generalize" :dir :system)
;; (include-book "clause-processors/find-subterms" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(local (include-book "std/lists/resize-list" :dir :system))

(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))

(in-theory (disable mv-nth))



(defsection fieldinfo-p

  (std::defaggregate array-fieldinfo
    ((tr-key symbolp "key under which the typed record is stored")
     (size-key symbolp "key under which the array size is stored")
     ;; (type symbolp "identifier for the kind of typed record")
     )
    :layout :tree
    :tag :array)

  (std::defaggregate scalar-fieldinfo
    ((key symbolp "key under which the typed record is stored")
     ;; (type symbolp "identifier for element type")
     )
    :layout :tree
    :tag :scalar)

  (defund fieldinfo-p (x)
    (declare (xargs :guard t))
    (mbe :logic (or (array-fieldinfo-p x)
                    (scalar-fieldinfo-p x))
         :exec (case (acl2::tag x)
                 (:array (array-fieldinfo-p x))
                 (:scalar (scalar-fieldinfo-p x))))))


(local
 (defthm array-tag-when-fieldinfo-p
   (implies (fieldinfo-p x)
            (equal (equal (acl2::tag x) :array)
                   (array-fieldinfo-p x)))
   :hints(("Goal" :in-theory (enable fieldinfo-p)))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local
 (defthm scalar-tag-when-fieldinfo-p
   (implies (fieldinfo-p x)
            (equal (equal (acl2::tag x) :scalar)
                   (scalar-fieldinfo-p x)))
   :hints(("Goal" :in-theory (enable fieldinfo-p)))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))


(defun field-map-p (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (fieldinfo-p (car x))
         (field-map-p (cdr x)))))

(defun field-map-collect-names (x)
  (declare (xargs :guard (field-map-p x)))
  (if (atom x)
      nil
    (let ((rest (field-map-collect-names (cdr x))))
      (case (acl2::tag (car x))
        (:array (cons (array-fieldinfo->tr-key (car x))
                      (cons (array-fieldinfo->size-key (car x))
                            rest)))
        (otherwise (cons (scalar-fieldinfo->key (car x)) rest))))))

(local
 (defthm eqlable-listp-of-field-map-collect-names
   (implies (field-map-p x)
            (eqlable-listp (field-map-collect-names x)))))

(defun field-map-well-formedp (x)
  (declare (xargs :guard t))
  (and (field-map-p x)
       (no-duplicatesp (field-map-collect-names x))))


(defun field-map-key-lookup (key map)
  (declare (xargs :guard (and (symbolp key)
                              (field-map-p map))
                  :verify-guards nil))
  (if (atom map)
      (mv nil nil)
    (mv-let (type idx)
      (case (acl2::tag (car map))
        (:array (b* (((array-fieldinfo x) (car map)))
                  (cond ((eq key x.tr-key)   (mv :array 0))
                        ((eq key x.size-key) (mv :size 0))
                        (t (mv nil nil)))))
        (:scalar (b* (((scalar-fieldinfo x) (car map)))
                   (cond ((eq key x.key) (mv :scalar 0))
                         (t (mv nil nil)))))
        (t (mv nil nil)))
      (if type
          (mv type idx)
        (mv-let (type idx)
          (field-map-key-lookup key (cdr map))
          (if type
              (mv type (+ 1 idx))
            (mv nil nil)))))))

(local
 (defthm natp-of-field-map-key-lookup
   (implies (mv-nth 0 (field-map-key-lookup key map))
            (natp (mv-nth 1 (field-map-key-lookup key map))))
   :rule-classes :type-prescription))

(defund-nx field-map-key-lookup-recur (mv)
  (if (mv-nth 0 mv)
      (mv (mv-nth 0 mv) (+ 1 (mv-nth 1 mv)))
    (mv nil nil)))

(in-theory (disable (field-map-key-lookup-recur)))

(defthm field-map-key-lookup-recur-open
  (equal (field-map-key-lookup-recur (list type idx))
         (if type
             (mv type (+ 1 idx))
           (mv nil nil)))
  :hints(("Goal" :in-theory (enable field-map-key-lookup-recur))))

(defthm field-map-key-lookup-open
  (implies (syntaxp (quotep map))
           (equal (field-map-key-lookup key map)
                  (if (atom map)
                      (mv nil nil)
                    (mv-let (type idx)
                      (case (acl2::tag (car map))
                        (:array (b* (((array-fieldinfo x) (car map)))
                                  (cond ((eq key x.tr-key)   (mv :array 0))
                                        ((eq key x.size-key) (mv :size 0))
                                        (t (mv nil nil)))))
                        (:scalar (b* (((scalar-fieldinfo x) (car map)))
                                   (cond ((eq key x.key) (mv :scalar 0))
                                         (t (mv nil nil)))))
                        (t (mv nil nil)))
                      (if type
                          (mv type idx)
                        (field-map-key-lookup-recur
                         (field-map-key-lookup key (cdr map))))))))
  :hints(("Goal" :in-theory (enable field-map-key-lookup
                                    field-map-key-lookup-recur))))


(local
 (defthm reverse-of-field-map-key-lookup
   (mv-let (type idx)
     (field-map-key-lookup key map)
     (implies (and type (field-map-well-formedp map))
              (let ((entry (nth idx map)))
                (and (implies (eq type :array)
                              (and (equal (acl2::tag entry) :array)
                                   (equal (array-fieldinfo->tr-key entry) key)))
                     (implies (eq type :size)
                              (and (equal (acl2::tag entry) :array)
                                   (equal (array-fieldinfo->size-key entry) key)))
                     (implies (eq type :scalar)
                              (and (equal (acl2::tag entry) :scalar)
                                   (equal (scalar-fieldinfo->key entry) key)))))))))

(local
 (defthm not-equal-nth-by-not-in-field-map
   (implies (not (member b (field-map-collect-names map)))
            (let ((entry (nth n map)))
              (and (implies (equal (acl2::tag entry) :array)
                            (and (not (equal (array-fieldinfo->tr-key entry) b))
                                 (not (equal (array-fieldinfo->size-key entry) b))))
                   (implies (equal (acl2::tag entry) :scalar)
                            (not (equal (scalar-fieldinfo->key entry) b))))))))

(local
 (defthm field-map-key-lookup-by-nth
   (implies (field-map-well-formedp map)
            (let ((entry (nth n map)))
              (and (implies (equal (acl2::tag entry) :array)
                            (and (mv-let (type idx)
                                   (field-map-key-lookup
                                    (array-fieldinfo->tr-key entry) map)
                                   (and (equal type :array)
                                        (equal idx (nfix n))))
                                 (mv-let (type idx)
                                   (field-map-key-lookup
                                    (array-fieldinfo->size-key entry) map)
                                   (and (equal type :size)
                                        (equal idx (nfix n))))))
                   (implies (equal (acl2::tag entry) :scalar)
                            (mv-let (type idx)
                              (field-map-key-lookup
                               (scalar-fieldinfo->key entry) map)
                              (and (equal type :scalar)
                                   (equal idx (nfix n))))))))
   :hints (("goal" :induct (nth n map)))))

(local
 (defthm keys-same-when-field-map-well-formedp
   (implies (field-map-well-formedp map)
            (b* ((x1 (nth nx1 map))
                 ((array-fieldinfo a1) x1)
                 ((scalar-fieldinfo s1) x1)
                 (x2 (nth nx2 map))
                 ((array-fieldinfo a2) x2)
                 ((scalar-fieldinfo s2) x2))
              (and (implies (and (equal (acl2::tag x1) :array)
                                 (equal (acl2::tag x2) :array))
                            (and (equal (equal a1.tr-key a2.tr-key)
                                        (equal (nfix nx1) (nfix nx2)))
                                 (not (equal a1.tr-key a2.size-key))
                                 (equal (equal a1.size-key a2.size-key)
                                        (equal (nfix nx1) (nfix nx2)))))
                   (implies (and (equal (acl2::tag x1) :array)
                                 (equal (acl2::tag x2) :scalar))
                            (and (not (equal a1.tr-key s2.key))
                                 (not (equal a1.size-key s2.key))))
                   (implies (and (equal (acl2::tag x1) :scalar)
                                 (equal (acl2::tag x2) :scalar))
                            (and (equal (equal s1.key s2.key)
                                        (equal (nfix nx1) (nfix nx2)))
                                 (equal (equal s1.key s2.key)
                                        (equal (nfix nx1) (nfix nx2))))))))
   :hints (("goal" :use ((:instance field-map-key-lookup-by-nth (n nx1))
                         (:instance field-map-key-lookup-by-nth (n nx2)))
            :in-theory (acl2::e/d* (acl2::arith-equiv-forwarding)
                                   (field-map-key-lookup-by-nth))
            :do-not-induct t))))



(encapsulate
  (((rstobj-field-map) => *)
   ((rstobj-tr-get * * *) => *)
   ((rstobj-tr-set * * * *) => *)
   ((rstobj-tr-fix * *) => *)
   ((rstobj-tr-default *) => *)
   ((rstobj-tr-elem-p * *) => *)
   ((rstobj-scalar-fix * *) => *)
   ((rstobj-scalar-elem-p * *) => *))

  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)

  (local (defun rstobj-field-map () nil))
  (local (defun rstobj-tr-get (name i tr) nil))
  (local (defun rstobj-tr-set (name i v tr) nil))
  (local (defun rstobj-tr-fix (name v) v))
  (local (defun rstobj-tr-default (name) nil))
  (local (defun rstobj-tr-elem-p (name v) t))
  (local (defun rstobj-scalar-fix (name v) v))
  (local (defun rstobj-scalar-elem-p (name v) t))


  (defthm field-map-well-formedp-of-rstobj-field-map
    (field-map-well-formedp (rstobj-field-map)))

  (defthm rstobj-tr-get-of-set-diff
    (implies (not (equal i1 i2))
             (equal (rstobj-tr-get name i1 (rstobj-tr-set name i2 v tr))
                    (rstobj-tr-get name i1 tr))))

  (defthm rstobj-tr-elem-p-of-get
    (implies (equal (mv-nth 0 (field-map-key-lookup name (rstobj-field-map))) :array)
             (rstobj-tr-elem-p name (rstobj-tr-get name i tr))))

  (defthm rstobj-tr-get-of-set-same
    (implies (equal (mv-nth 0 (field-map-key-lookup name (rstobj-field-map))) :array)
             (equal (rstobj-tr-get name i (rstobj-tr-set name i v tr))
                    (rstobj-tr-fix name v))))

  (defthm rstobj-tr-fix-of-elem-p
    (implies (rstobj-tr-elem-p name v)
             (equal (rstobj-tr-fix name v) v)))

  (defthm rstobj-tr-elem-p-of-fix
    (implies (equal (mv-nth 0 (field-map-key-lookup name (rstobj-field-map))) :array)
             (rstobj-tr-elem-p name (rstobj-tr-fix name v))))

  (defthm rstobj-scalar-fix-of-elem-p
    (implies (rstobj-scalar-elem-p name v)
             (equal (rstobj-scalar-fix name v) v)))

  (defthm rstobj-scalar-elem-p-of-fix
    (implies (equal (mv-nth 0 (field-map-key-lookup name (rstobj-field-map))) :scalar)
             (rstobj-scalar-elem-p name (rstobj-scalar-fix name v))))

  (defthm rstobj-tr-get-of-nil
    (equal (rstobj-tr-get name i nil)
           (rstobj-tr-default name))))




(defun-sk rstobj-field-corr (rstobj$c rstobj$a)
  (forall (idx i)
          (let ((entry (nth idx (rstobj-field-map))))
            (and (implies (equal (acl2::tag entry) :array)
                          ;; array
                          (b* (((array-fieldinfo x) entry)
                               (arr (nth idx rstobj$c))
                               (tr  (g x.tr-key rstobj$a)))
                            (and (implies (natp i)
                                          (equal (rstobj-tr-get x.tr-key i tr)
                                                 (if (< i (len arr))
                                                     (nth i arr)
                                                   (rstobj-tr-default x.tr-key))))
                                 (equal (g x.size-key rstobj$a)
                                        (len arr)))))
                 (implies (equal (acl2::tag entry) :scalar)
                          (b* (((scalar-fieldinfo x) entry))
                            (equal (g x.key rstobj$a)
                                   (nth idx rstobj$c)))))))
  :rewrite :direct)


(in-theory (disable rstobj-field-corr
                    rstobj-field-corr-necc))

(defthmd rstobj-field-corr-of-size-key
  (mv-let (keytype idx)
    (field-map-key-lookup szkey (rstobj-field-map))
    (implies (and (rstobj-field-corr rstobj$c rstobj$a)
                  (equal keytype :size))
             (equal (g szkey rstobj$a)
                    (len (nth idx rstobj$c)))))
  :hints (("goal" :use ((:instance rstobj-field-corr-necc
                         (idx (mv-nth 1 (field-map-key-lookup szkey (rstobj-field-map)))))))))

(defthmd rstobj-field-corr-of-scalar-key
  (mv-let (keytype idx)
    (field-map-key-lookup sckey (rstobj-field-map))
    (implies (and (rstobj-field-corr rstobj$c rstobj$a)
                  (equal keytype :scalar))
             (equal (g sckey rstobj$a)
                    (nth idx rstobj$c))))
  :hints (("goal" :use ((:instance rstobj-field-corr-necc
                         (idx (mv-nth 1 (field-map-key-lookup sckey (rstobj-field-map)))))))))

(defthmd rstobj-field-corr-of-tr-key
  (mv-let (keytype idx)
    (field-map-key-lookup trkey (rstobj-field-map))
    (implies (and (rstobj-field-corr rstobj$c rstobj$a)
                  (equal keytype :array)
                  (natp i))
             (equal (rstobj-tr-get trkey i (g trkey rstobj$a))
                    (if (< i (len (nth idx rstobj$c)))
                        (nth i (nth idx rstobj$c))
                      (rstobj-tr-default trkey)))))
  :hints (("goal" :use ((:instance rstobj-field-corr-necc
                         (idx (mv-nth 1 (field-map-key-lookup trkey (rstobj-field-map))))))
           :in-theory (disable nth))))

(local (in-theory (enable rstobj-field-corr-necc)))

(defthmd rstobj-field-corr-of-update-scalar
  (implies (and (rstobj-field-corr rstobj$c rstobj$a)
                (equal (acl2::tag (nth idx (rstobj-field-map))) :scalar)
                (equal (scalar-fieldinfo->key (nth idx (rstobj-field-map))) key)
                (equal v (rstobj-scalar-fix key v)))
           (rstobj-field-corr (update-nth idx v rstobj$c)
                              (s key v rstobj$a)))
  :hints (("goal" :in-theory (acl2::e/d* (acl2::arith-equiv-forwarding)
                                         (nfix))
           :cases ((nth idx (rstobj-field-map)))
           :do-not-induct t)
          (and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))



(defthmd rstobj-field-corr-of-update-array
  (implies (and (rstobj-field-corr rstobj$c rstobj$a)
                (equal (acl2::tag (nth idx (rstobj-field-map))) :array)
                (equal (array-fieldinfo->tr-key (nth idx (rstobj-field-map))) key)
                (equal tr1 (rstobj-tr-set key i v (g key rstobj$a)))
                (equal v (rstobj-tr-fix key v))
                (natp i)
                (< i (len (nth idx rstobj$c))))
           (rstobj-field-corr (update-nth idx (update-nth i v (nth idx rstobj$c))
                                      rstobj$c)
                          (s key tr1 rstobj$a)))
  :hints (("goal" :in-theory (acl2::e/d* (acl2::g-of-s-redux acl2::arith-equiv-forwarding)
                                   (nfix))
           :cases ((nth idx (rstobj-field-map)))
           :do-not-induct t)
          (and stable-under-simplificationp
               `(:expand (,(car (last clause))))))
  :otf-flg t)


(defthmd rstobj-field-corr-of-grow-array
  (implies (and (rstobj-field-corr rstobj$c rstobj$a)
                (equal (acl2::tag (nth idx (rstobj-field-map))) :array)
                (equal (array-fieldinfo->size-key (nth idx (rstobj-field-map))) size-key)
                (natp new-size)
                (<= (len (nth idx rstobj$c)) new-size)
                (equal default (rstobj-tr-default
                                (array-fieldinfo->tr-key (nth idx (rstobj-field-map))))))
           (rstobj-field-corr (update-nth idx
                                          (resize-list (nth idx rstobj$c) new-size default)
                                          rstobj$c)
                              (s size-key new-size rstobj$a)))
  :hints (("goal" :in-theory (acl2::e/d* (acl2::g-of-s-redux acl2::arith-equiv-forwarding)
                                   (nfix))
           :cases ((nth idx (rstobj-field-map)))
           :do-not-induct t)
          (and stable-under-simplificationp
               `(:expand (,(car (last clause))))))
  :otf-flg t)

(defthmd rstobj-field-corr-of-empty-array
  (implies (and (rstobj-field-corr rstobj$c rstobj$a)
                (equal (acl2::tag (nth idx (rstobj-field-map))) :array)
                (equal (array-fieldinfo->tr-key (nth idx (rstobj-field-map))) tr-key)
                (equal (array-fieldinfo->size-key (nth idx (rstobj-field-map))) size-key))
           (rstobj-field-corr (update-nth idx nil rstobj$c)
                              (s tr-key nil (s size-key 0 rstobj$a))))
  :hints (("goal" :in-theory (acl2::e/d* (acl2::g-of-s-redux acl2::arith-equiv-forwarding)
                                   (nfix))
           :cases ((nth idx (rstobj-field-map)))
           :do-not-induct t)
          (and stable-under-simplificationp
               `(:expand (,(car (last clause))))))
  :otf-flg t)

