; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

(in-package "GACC")

;try to include less of super-ihs:
(include-book "../super-ihs/super-ihs")
(include-book "../lists/memberp")
(include-book "../lists/repeat")
(include-book "../bags/basic")
(include-book "../lists/find-index")

;;
;; logapp-list
;;

;Append j to each element of i-list.  I'm not thrilled with the order of the
;parameters here (I think j should come first, but they match the order for
;logpp).
(defund logapp-list (size i-list j)
  (declare (xargs :guard (integer-listp i-list))
           (type integer j)
           (type (integer 0 *) size))
  (if (consp i-list)
      (cons (logapp size (car i-list) j)
            (logapp-list size (cdr i-list) j))
    nil))

(defthm integer-listp-of-logapp-list
  (integer-listp (logapp-list size i-list j))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm logapp-list-of-cons
  (equal (logapp-list size (cons i i-list) j)
         (cons (logapp size i j) (logapp-list size i-list j)))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm consp-of-logapp-list
  (equal (consp (logapp-list size i-list j))
         (consp i-list))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm car-of-logapp-list
  (equal (car (logapp-list size i-list j))
         (if (consp i-list)
             (logapp size (car i-list) j)
           nil))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm cdr-of-logapp-list
  (equal (cdr (logapp-list size i-list j))
         (logapp-list size (cdr i-list) j))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm logapp-list-when-i-list-is-not-a-consp
  (implies (not (consp i-list))
           (equal (logapp-list size i-list j)
                  nil))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm logapp-list-when-j-is-not-an-integerp
  (implies (not (integerp j))
           (equal (logapp-list size i-list j)
                  (logapp-list size i-list 0)))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm len-of-logapp-list
  (equal (len (logapp-list size i-list j))
         (len i-list))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm nthcdr-of-logapp-list
  (equal (nthcdr n (logapp-list size ilist j))
         (logapp-list size (nthcdr n ilist) j))
  :hints (("Goal" :in-theory (enable nthcdr logapp-list))))

(defthm not-memberp-of-logapp-list
  (implies (not (equal (ifix j1) (ifix j2)))
           (not (list::memberp (logapp '16 offset1 j1) (logapp-list '16 vals j2))))
  :hints (("Goal" :in-theory (enable logapp-list
                                     acl2::equal-logapp-x-y-z))))

;move
(defthmd NTH-0-BECOMES-CAR-gen
  (implies (zp n)
           (equal (NTH N VALS)
                  (car vals))))

(defthm nth-of-logapp-list
  (equal (nth n (logapp-list size vals j))
         (if (< (nfix n) (len vals))
             (logapp size (nth n vals) j)
           nil))
  :hints (("Goal" :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (LIST::NTH-0-BECOMES-CAR
                             NTH-0-BECOMES-CAR-gen
                            (:induction nth)
                            logapp-list)
                           ( ACL2::EQUAL-LOGAPP-X-Y-Z ;bzo
                            ACL2::EQUAL-LOGAPP-X-Y-Z-CONSTANTS
                            )))))

;; unique of logapp-list?


;;
;; LOGEXT-LIST
;;

(defund logext-list (size i-list)
  (declare (xargs :guard (integer-listp i-list))
           (type (integer 1 *) size))
  (if (consp i-list)
      (cons (acl2::logext size (car i-list))
            (logext-list size (cdr i-list)))
    nil))

(defthm len-of-logext-list
  (equal (len (logext-list size i-list))
         (len i-list))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm consp-of-logext-list
  (equal (consp (logext-list size i-list))
         (consp i-list))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm car-of-logext-list
  (equal (car (logext-list size i-list))
         (if (consp i-list)
             (acl2::logext size (car i-list))
           nil))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm cdr-of-logext-list
  (equal (cdr (logext-list size i-list))
         (logext-list size (cdr i-list)))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm logext-list-of-cons
 (equal (logext-list size (cons i i-list))
        (cons (acl2::logext size i) (logext-list size i-list)))
 :hints (("Goal" :in-theory (enable logext-list))))

(defthm nthcdr-of-logext-list
  (equal (nthcdr n (logext-list size ads))
         (logext-list size (nthcdr n ads)))
  :hints (("Goal" :in-theory (enable nthcdr logext-list))))

;;
;; LOGCDR-LIST
;;

(defun logcdr-list (vals)
  (if (endp vals)
      nil
    (cons (acl2::logcdr (car vals))
          (logcdr-list (cdr vals)))))

;;
;; IFIX-LIST
;;

(defun ifix-list (vals)
  (if (endp vals)
      vals ;return nil instead?
    (cons (ifix (car vals)) (ifix-list (cdr vals)))))

(defthm ifix-list-does-nothing
  (implies (integer-listp vals)
           (equal (ifix-list vals)
                  vals)))

(defthm integer-listp-of-logext-list
  (integer-listp (logext-list n x))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm logcdr-list-of-append
  (equal (gacc::logcdr-list (append x y))
         (append (gacc::logcdr-list x)  (gacc::logcdr-list y))))

;;
;; LOGHEAD-LIST
;;

(defun loghead-list (size i-list)
  (declare (xargs :guard (integer-listp i-list))
           (type (integer 1 *) size))
  (if (endp i-list)
      nil
    (cons (loghead size (car i-list))
          (loghead-list size (cdr i-list)))))

(defthm loghead-list-of-append
  (equal (gacc::loghead-list n (append x y))
         (append (gacc::loghead-list n x)
                 (gacc::loghead-list n y))))

(defthm integer-listp-of-loghead-list
  (integer-listp (loghead-list size i-list))
  :hints (("Goal" :in-theory (enable loghead-list))))

(defthm loghead-list-when-n-is-not-an-integerp
  (implies (not (integerp n))
           (equal (loghead-list n x)
                  (repeat (len x) 0))))

(defthm memberp-of-logapp-and-logapp-list-hack
  (equal (list::memberp (logapp '16 offset denvr) (logapp-list '16 x denvr))
         (and (consp x)
              (list::memberp (loghead 16 offset) (loghead-list '16 x))))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm logext-list-when-i-list-is-not-a-consp
  (implies (not (consp i-list))
           (equal (logext-list size i-list)
                  nil))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm memberp-of-logext-and-logext-list
  (implies (and (integerp n)
                (< 0 n))
           (equal (list::memberp (logext n a) (logext-list n x))
                  (list::memberp (loghead n a) (loghead-list n x)))))

(defthmd logapp-list-of-loghead
  (implies (and             ; (integer-listp i-list)
            (integerp size1)
            (integerp size2)
            (<= 0 size1)
            (<= 0 size2)
            )
           (equal (logapp-list size1 i-list (loghead size2 j))
                  (loghead-list (+ size1 size2)  (logapp-list size1 i-list j))))
  :hints (("Goal" :in-theory (e/d (logapp-list
                                   ACL2::LOGTAIL-LOGHEAD-BETTER)
                                  (ACL2::LOGHEAD-LOGTAIL)))))


(defthm logext-list-of-loghead-list
  (implies (and (integerp size)
                (< 0 size))
           (equal (logext-list size (loghead-list size vals))
                  (logext-list size vals)))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm logext-list-of-loghead-list-gen
  (implies (and (<= size1 size2)
                (< 0 size2)
                (integerp size1)
                (integerp size2)
                )
           (equal (logext-list size1 (loghead-list size2 vals))
                  (logext-list size1 vals)))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm logext-list-of-append
  (equal (logext-list size (append vals1 vals2))
         (append (logext-list size vals1) (logext-list size vals2)))
  :hints (("Goal" :in-theory (enable logext-list))))

(defthm nth-of-logext-list
  (equal (nth n (logext-list size vals))
         (if (< (nfix n) (len vals))
             (logext size (nth n vals))
           nil))
  :hints (("Goal" :in-theory (enable logext-list nth))))


;bzo dup?
(defun unsigned-byte-p-list (size vals)
  (if (endp vals)
      t
    (and (unsigned-byte-p size (car vals))
         (unsigned-byte-p-list size (cdr vals)))))

(defthm unsigned-byte-p-list-of-logapp-list-hack
  (implies (and (<= 0 denvr) ;drop?
                (integerp denvr))
           (equal (unsigned-byte-p-list 31 (logapp-list 16 i denvr))
                  (or (not (consp i))
                      (unsigned-byte-p 15 denvr))))
  :hints (("Goal" :in-theory (enable logapp-list))))





(defthm logext-list-of-logapp-list
  (implies (and (< size2 size)
                (integerp size)
                (integerp size2)
                (<= 0 size2)
                )
  (equal (logext-list size (logapp-list size2 x denvr))
         (logapp-list size2 x (logext (- size size2) denvr))))
  :hints (("Goal" :in-theory (enable logext-list logapp-list acl2::logext-logapp))))

;bzo nested inductions
(defthm disjoint-of-two-calls-to-logapp-list
  (equal (disjoint (logapp-list 16 x1 y1) (logapp-list 16 x2 y2))
         (or (not (equal (ifix y1) (ifix y2)))
             (disjoint (loghead-list 16 x1) (loghead-list 16 x2))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable logapp-list))))

(defthm logapp-list-when-j-is-zero
  (equal (logapp-list size vals 0)
         (loghead-list size vals)))

(defun logtail-list (pos ivals)
  (if (endp ivals)
      nil
    (cons (acl2::logtail pos (car ivals))
          (logtail-list pos (cdr ivals)))))


;bzo param aren't really envs
(defthm hack-for-code-data-clash
  (implies (not (memberp (loghead 15 (logtail 16 denvr)) (loghead-list 15 (logtail-list 17 cenvs))))
           (not (memberp (logapp 1 0 denvr) cenvs)))
  :hints (("Goal" :in-theory (enable memberp))))

(defthm hack-for-code-data-clash2
  (implies (not (memberp (loghead 15 (logtail 16 denvr)) (loghead-list 15 (logtail-list 17 cenvs))))
           (not (memberp (logapp 1 1 denvr) cenvs)))
  :hints (("Goal" :in-theory (e/d (memberp ACL2::LOGTAIL-LOGHEAD-BETTER) (acl2::LOGHEAD-LOGTAIL)))))

;bzo gen
(defthm logtail-list-of-logapp-list-17-16
  (equal (logtail-list 17 (logapp-list 16 ivals j))
         (repeat (len ivals) (acl2::logcdr j))))

(defthm loghead-list-of-repeat-15
  (equal (loghead-list 15 (repeat n v))
         (repeat n  (loghead 15 v)))
  :hints (("Goal" :in-theory (enable loghead-list repeat))))

(defthm logapp-list-non-memberp-hack
  (implies (not (equal (loghead 15 j) (logtail 16 (loghead 31 (car y)))))
           (not (memberp (car y) (logapp-list 16 ivals j))))
  :hints (("Goal" :in-theory (enable logapp-list))))

(defthm disjoint-of-logapp-list-hack
  (implies (not (memberp (loghead 15 j) (loghead-list 15 (logtail-list 16 y))))
           (disjoint (logapp-list 16 ivals j) y))
  :hints (("Goal" :expand ((disjoint y (logapp-list 16 ivals j))))))

;bzo gen
(defthm logtail-list-of-logcdr-list
  (equal (logtail-list '16 (logcdr-list vals))
         (logtail-list 17 vals)))
;rr
(defthm count-of-logapp-list
  (implies (integer-listp vals)
           (equal (bag::count a (logapp-list 16 vals j))
                  (if (and (integerp a)
                           (equal (ifix j) (acl2::logtail 16 a)))
                      (bag::count (loghead 16 a) (loghead-list 16 vals))
                    0)))
  :hints (("Goal" :in-theory (enable logapp-list acl2::equal-logapp-x-y-z))))

(defthm memberp-of-loghead-list
  (implies (list::memberp a x)
           (list::memberp (loghead 16 a)
                          (loghead-list 16 x))))


(local (defun double-cdr-induct (x y)
  (if (endp x)
      (list x y)
    (double-cdr-induct (cdr x) (cdr y)))))

(defcong list::equiv equal (loghead-list size vals) 2
  :hints (("Goal" :induct (double-cdr-induct vals vals-equiv))))


(defthm loghead-list-of-remove-1
  (implies (list::memberp a x)
           (bag::perm (loghead-list 16 (bag::remove-1 a x))
                      (bag::remove-1 (loghead 16 a)
                                     (loghead-list 16 x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable list::memberp bag::remove-1 loghead-list))))


(defthm loghead-list-of-remove-1-both
  (bag::perm (LOGHEAD-LIST 16 (BAG::REMOVE-1 a x))
             (if (list::member a x)
                 (bag::remove-1 (loghead 16 a) (LOGHEAD-LIST 16 x) )
               (LOGHEAD-LIST 16 x))))

(local (include-book "../bags/pick-a-point")) ;bzo make non-local?

(defthm subbagp-of-two-loghead-list-calls
  (implies (bag::subbagp vals1 vals2)
           (bag::subbagp (loghead-list 16 vals1)
                         (loghead-list 16 vals2)))
  :hints (("Goal" :expand (bag::subbagp vals1 vals2)
           :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (loghead-list bag::subbagp) (bag::subbagp-cdr-remove-1-rewrite ;bzo
                                                        )))))

;move
(defthm subbagp-of-two-logapp-list-calls
  (implies (and (bag::subbagp vals1 vals2)
                (integer-listp vals1)
                (integer-listp vals2)
;               (integerp j)
                )
           (bag::subbagp (logapp-list '16 vals1 j)
                         (logapp-list '16 vals2 j)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (logapp-list) ( ;bag::memberp-of-remove-bag bag::subbagp-of-cons
                                          )))))

;bzo see loghead-list-of-logapp-list
;move up
(defthm loghead-list-of-logapp-list-same-size
  (equal (loghead-list size (logapp-list size vals j))
         (loghead-list size vals)))

;move bzo rename
(defthm disjoint-of-two-loghead-list-calls
  (implies (and (integerp n)
                (< 0 n))
           (equal (disjoint (logext-list n x)
                            (logext-list n y))
                  (disjoint (loghead-list n x)
                            (loghead-list n y)))))

(defthm loghead-list-does-nothing
  (implies (unsigned-byte-p-list width x)
           (equal (loghead-list width x)
                  (list::fix x)
                  ))
  :hints (("Goal" :in-theory (enable loghead-list))))

(defthm unique-of-logext-list
  (implies (and (integerp n) (< 0 n))
           (equal (unique (logext-list n x))
                  (unique (loghead-list n x)))))

(defthm loghead-list-of-loghead-list
  (equal (loghead-list n (loghead-list n vals))
         (loghead-list n vals)))

(defthm consp-of-loghead-list
  (equal (consp (loghead-list size i-list))
         (consp i-list))
  :hints (("Goal" :in-theory (enable loghead-list))))

(defthm car-of-loghead-list
  (equal (car (loghead-list size i-list))
         (if (consp i-list)
             (loghead size (car i-list))
           nil))
  :hints (("Goal" :in-theory (enable loghead-list))))

(defthm nthcdr-of-loghead-list
  (equal (nthcdr n (loghead-list size ads))
         (loghead-list size (nthcdr n ads)))
  :hints (("Goal" :in-theory (enable nthcdr loghead-list))))

(defthm nth-of-loghead-list
  (equal (nth n (loghead-list size vals))
         (if (< (nfix n) (len vals))
             (loghead size (nth n vals))
           nil))
  :hints (("Goal" :in-theory (enable loghead-list nth))))

;bzo kill the non-gen
(defthm loghead-list-of-logapp-list
  (implies (and (< size2 size)
                (integerp size)
                (integerp size2)
                (<= 0 size2))
           (equal (loghead-list size (logapp-list size2 x denvr))
                  (logapp-list size2 x (loghead (- size size2) denvr))))
  :hints
  (("Goal" :in-theory (enable loghead-list
                              logapp-list acl2::loghead-logapp))))

(theory-invariant (incompatible (:rewrite loghead-list-of-logapp-list)
                                (:rewrite logapp-list-of-loghead)))


;adapt this to generalize  LOGHEAD-LIST-of-LOGAPP-LIST
;; (defthm logapp-list-of-loghead
;;   (implies (and             ; (integer-listp i-list)
;;             (integerp size1)
;;             (integerp size2)
;;             (<= 0 size1)
;;             (<= 0 size2)
;;             )
;;            (equal (logapp-list size1 i-list (loghead size2 j))
;;                   (loghead-list (+ size1 size2)  (logapp-list size1 i-list j))))
;;   :hints (("Goal" :in-theory (e/d (logapp-list
;;                                    ACL2::LOGTAIL-LOGHEAD-BETTER)
;;                                   (ACL2::LOGHEAD-LOGTAIL)))))

;;
;; WINTLIST
;;

;Convert the bytes in LIST to one big bit vector.
;Note that the bytes appearing first in LIST appear as the lower-order bytes of the result.
;Eric doesn't like the name of this.

;Eric replaced wcons with logapp.
(defund wintlist (list)
  (declare (xargs :guard (integer-listp list)))
  (if (consp list)
      (acl2::logapp 8 (car list) (wintlist (cdr list)))
    0))

(defthm wintlist-of-cons
  (equal (wintlist (cons byte byte-list))
         (acl2::logapp 8 byte (wintlist byte-list)))
  :hints (("Goal" :in-theory (enable wintlist))))

(defthm wintlist-when-list-is-not-a-consp
  (implies (not (consp list))
           (equal (wintlist list)
                  0))
  :hints (("Goal" :in-theory (enable wintlist))))

;could gen the 8?
(defthm loghead-8-of-wintlist
  (equal (acl2::loghead 8 (wintlist lst))
         (if (consp lst)
             (acl2::loghead 8 (car lst))
           0))
  :hints (("Goal" :expand (wintlist lst))))

;could gen the 8?
(defthm logtail8-of-wintlist
  (equal (acl2::logtail 8 (wintlist list))
         (if (endp list)
             0
           (wintlist (cdr list)))))

;bzo gen!
(defthm loghead-16-of-wintlist
  (equal (loghead 16 (wintlist byte-list))
         (wintlist (firstn 2 byte-list)))
  :hints (("Goal" :in-theory (enable wintlist))))

(defthm wintlist-equal-0-rewrite
  (equal (equal 0 (wintlist lst))
         (equal (loghead-list 8 lst)
                (repeat (len lst) 0))))

;;
;; ENLISTW
;;

;Return a list of the SIZE low-order bytes of V.  Note that the low-order
;bytes of V appear first in the resulting list.  I wanted to get rid of the
;size parameter but realized that would cause problems because we can't tell
;by looking at v what size it is (e.g., what size is 0?).  Eric isn't thrilled
;with the name of this.

;Eric replaced wcar with loghead and wcdr with logtail.
;bzo Add guards? (may require adding ifixes here until we improve the guards on loghead and logtail). -ews
(defund enlistw (size v)
  (declare (type integer v)
           (type (integer 0 *) size))
  (if (zp size)
      nil
    (cons (acl2::loghead 8 v)
          (enlistw (1- size) (acl2::logtail 8 v)))))

(defthm enlistw-when-size-is-not-an-integerp
  (implies (not (integerp size))
           (equal (enlistw size v)
                  nil))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthm enlistw-when-size-is-non-positive
  (implies (<= size 0)
           (equal (enlistw size v)
                  nil))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthm enlistw-when-size-is-one
  (equal (enlistw 1 v)
         (list (acl2::loghead 8 v)))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthmd enlistw-constant-opener
  (implies (and (syntaxp (quotep k))
                (not (zp k)))
           (equal (enlistw k val)
                  (cons (loghead 8 val)
                        (enlistw (1- k) (logtail 8 val)))))
  :hints (("Goal" :in-theory (enable enlistw))))

;car and cdr of enlistw?

(defthm car-of-enlistw
  (equal (car (enlistw size v))
         (if (zp size)
             nil
           (acl2::loghead 8 v)))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthm cdr-of-enlistw
  (equal (cdr (enlistw size v))
         (if (zp size)
             nil
           (enlistw (+ -1 size) (acl2::logtail 8 v))))
  :hints (("Goal" :expand (ENLISTW SIZE V))))

(defthm len-enlistw
  (equal (len (enlistw size v))
         (nfix size))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthm consp-of-enlistw
  (equal (consp (enlistw size v))
         (not (zp size)))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthm enlistw-of-1
  (equal (enlistw 1 v)
         (list (loghead 8 v)))
  :hints (("Goal" :expand  (enlistw 1 v)
           :in-theory (enable enlistw))))

(defthm enlistw-of-0
  (equal (enlistw size 0)
         (repeat size 0))
  :hints (("Goal" :in-theory (enable enlistw repeat))))

(encapsulate
 ()
 (local (defun elistw-induct (size1 size2 v)
          (if (zp size1)
              (list size1 size2 v)
            (elistw-induct (+ -1 size1) (+ -1 size2) (acl2::logtail 8 v)))))

 (defthm enlistw-wfixw
   (implies (<= (nfix size1) (nfix size2))
            (equal (enlistw size1 (acl2::loghead (* 8 (nfix size2)) v))
                   (enlistw size1 v)))
   :hints (("Goal" :induct (elistw-induct size1 size2 v)
            :in-theory (enable enlistw ;wfixw
                               )))))

;; (defthm enlistw-when-v-is-zero
;;   (equal (ENLISTW size 0)
;;          ...))

(defthm enlistw-when-v-is-not-an-integerp
  (implies (not (integerp v))
           (equal (enlistw size v)
                  (enlistw size 0)))
  :hints (("Goal" :in-theory (enable enlistw))))

;bzo ACL2::FLOOR-FL and other rtl rules are around

(encapsulate
 ()
 (local (defun elistw-induct2 (size1 size2 v)
          (if (zp size1)
              (list size1 size2 v)
            (elistw-induct2 (+ -1 size1) (+ -8 size2) (acl2::logtail 8 v)))))

;bzo rename
 (defthm enlistw-wfixn
   (implies (and (<= (* 8 size1) n)
                 (integerp n)
                 (<= 0 n)
                 )
            (equal (enlistw size1 (acl2::loghead n v))
                   (enlistw size1 v)))
   :hints (("goal" :induct (elistw-induct2 size1 n v)
            :do-not '(generalize eliminate-destructors)
            :in-theory (enable enlistw zp)))))


;; Fix each element of LIST to be an 8-bit byte.
;bzo guard.
(defund wfixlist (list)
  (declare (xargs :guard (integer-listp list)))
  (if (consp list)
      (cons (acl2::loghead 8 ;wfixn 8 1
                           (car list)) ;should this be  (wfixn 8 8 (car list))?
            (wfixlist (cdr list)))
    nil))

;; Check that each element of LIST is an 8-bit byte.
(defund wfixedlist (list)
  (declare (type t list))
  (if (consp list)
      (and (acl2::unsigned-byte-p 8 ;wintn 8 1
                  (car list))  ;should this be  (wintn 8 8 (car list))?
           (wfixedlist (cdr list)))
    (null list) ;maybe we don't want to do this check, now that we have nice list congruences??
    ))

(defthm wfixedlist-of-cons
  (equal (wfixedlist (cons elem list))
         (and (unsigned-byte-p 8 elem)
              (wfixedlist list)))
  :hints (("Goal" :in-theory (enable wfixedlist))))

(defthm wfixedlist-of-nthcdr
  (implies (gacc::wfixedlist lst)
           (gacc::wfixedlist (nthcdr n lst)))
  :hints (("Goal" :in-theory (enable nthcdr gacc::wfixedlist))))

(defthm wfixedlist-of-append
  (implies (true-listp x) ;annoying
           (equal (gacc::wfixedlist (append x y))
                  (and (gacc::wfixedlist x)
                       (gacc::wfixedlist y)))))

(defthm wfixedlist-wfixlist
  (implies (wfixedlist list)
           (equal (wfixlist list)
                  list))
  :hints (("Goal" :in-theory (enable wfixedlist wfixlist))))

;(local (in-theory (enable wfixn-rewrite-to-loghead))) ;bzo

(defthm enlistw-wintlist
  (implies (equal size (len list))
           (equal (enlistw size (wintlist list))
                  (wfixlist list)))
  :hints (("Goal" :in-theory (enable ;wcar ;bzo
                              enlistw
                              wfixlist
                              wintlist
                                     ))))

(defthm wintnlist-enlistw
  (equal (wintlist (enlistw size v))
         (;wfixw 8 size
          acl2::loghead (* 8 (nfix size))
          v))
  :hints (("goal" :in-theory (enable ;wintn
                                     ;open-wfixw
                              enlistw
                              ;wfixlist
                              wintlist
                              ))))

;bzo move
;rename
(defthm subbagp-hack-eric
  (implies (and (consp list1)
                (memberp (car list1) list2))
           (equal (subbagp (remove-1 (car list1) list2)
                           (cdr list1))
                  (subbagp list2 list1)))
  :hints (("Goal" :in-theory (disable bag::subbagp-implies-subbagp-cons-common
                                      bag::subbagp-of-cons)
           :do-not '(generalize eliminate-destructors)
           :use (:instance bag::subbagp-implies-subbagp-cons-common
                           (bag::a (car list1)) (bag::y (cdr list1)) (bag::x  (remove (car list1) list2))))))

;bzo move
;bzo loops with bag::count-of-cdr
(defthmd count-of-car-same
  (equal (bag::count (car x) x)
         (if (consp x)
             (+ 1 (bag::count (car x) (cdr x)))
           0)))

;bzo move
(defthmd subbagp-expand
  (equal (subbagp list2 list1)
         (if (not (consp list1))
             (not (consp list2))
           (if (memberp (car list1) list2)
               (subbagp (remove-1 (car list1) list2) (cdr list1))
             (subbagp list2 (cdr list1))))))


(defthm unsigned-byte-of-wintlist-forward-chaining
  (unsigned-byte-p (* 8 (len byte-list)) (wintlist byte-list))
  :rule-classes ((:forward-chaining :trigger-terms ((wintlist byte-list))))
  :hints (("Goal" :in-theory (enable wintlist))))

(defthm unsigned-byte-of-wintlist
  (implies (and (<= (* 8 (len byte-list)) n)
                (integerp n))
           (unsigned-byte-p n (wintlist byte-list)))
  :hints (("Goal" :in-theory (enable wintlist))))

(defthm wfixedlist-of-enlistw
  (wfixedlist (enlistw numbytes v))
  :hints (("Goal" :in-theory (enable wfixedlist enlistw))))

(defthm enlistw-iff
  (iff (enlistw numbytes v)
       (not (zp numbytes)))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthm enlistw-of-one-more
  (implies (and (syntaxp (not (quotep size))) ;don't unify (+ 1 size) with constants..
                (integerp size)
                (<= 0 size))
           (equal (ENLISTW (+ 1 size) v)
                  (CONS (LOGHEAD 8 V)
                        (ENLISTW SIZE (LOGTAIL 8 V)))))
  :hints (("Goal" :in-theory (enable enlistw))))

(defthm wfixedlist-when-byte-list-is-not-a-consp
  (implies (not (consp byte-list))
           (equal (wfixedlist byte-list)
                  (equal nil byte-list)
                  ))
  :hints (("Goal" :in-theory (enable wfixedlist))))

(encapsulate
 ()
 (local (defthm enlistw-equal-rewrite-helper
          (implies (and (integerp numbytes)
    ;                (<= 0 numbytes)
    ;                (true-listp byte-list)
                        (unsigned-byte-p (* 8 numbytes) v)
                        )
                   (equal (equal (enlistw numbytes v) byte-list)
                          (and (equal v (wintlist byte-list))
                               (equal numbytes (len byte-list))
                               (wfixedlist byte-list)
                               )))
          :rule-classes nil
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :in-theory (e/d ( ;wintlist wfixedlist
                                    ) ( enlistw-of-one-more
                                    ))
                   :induct (LEN BYTE-LIST)))))

 ;; do we want to go this way or the other way?
 (defthm enlistw-equal-rewrite
   (equal (equal (enlistw numbytes v) byte-list)
          (if (and (integerp numbytes)
                   (<= 0 numbytes))
              (and (equal (loghead (* 8 numbytes) v) (wintlist byte-list))
                   (equal numbytes (len byte-list))
                   (wfixedlist byte-list)
                   )
            (equal byte-list nil)))
   :hints (("Goal" :use (:instance enlistw-equal-rewrite-helper (v (loghead (* 8 numbytes) v)))))))

;bzo go the other way from  enlistw-equal-rewrite too?

;hmmm..
(defund my-wfixlist (numbytes byte-list)
  (if (zp numbytes)
      nil
    (cons (loghead 8 (car byte-list))
          (my-wfixlist (+ -1 numbytes) (cdr byte-list)))))

(defthm my-wfixlist-when-numbytes-is-not-positive
  (implies (<= numbytes 0)
           (equal (my-wfixlist numbytes byte-list)
                  nil))
  :hints (("Goal" :in-theory (enable my-wfixlist))))

;gen the numbytes
(defthm my-wfixlist-of-enlistw
  (equal (my-wfixlist numbytes (enlistw numbytes v))
         (enlistw numbytes v))
  :hints (("Goal" :in-theory (enable my-wfixlist enlistw))))


;no nice lemma for rd of wr-list?  well,, you get the nth val of vals, where n is the posn of ad in ads...
;this is all probably okay?  we can implement rx/wx functionality easily enough?


(defun enlistw-n-induct (size n v)
  (if (zp size)
      (+ n v)
      (enlistw-n-induct (1- size)(1- n) (logtail 8 v))))

(defthm nth-of-enlistw
  (implies (and (< n numbytes)
                (acl2::natp n)
                (acl2::natp numbytes)
                (integerp v)
                )
           (equal (nth n (enlistw numbytes v))
                  (loghead 8 (logtail (* 8 n) v))))
  :hints (("Goal" :induct (ENLISTW-n-induct numbytes n v)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable enlistw))))


(defun cdr-and-sub1-induct (x n)
  (if (endp x)
      (list x n)
    (cdr-and-sub1-induct (cdr x) (+ -1 n))))

(defthm logtail-of-wintlist
  (implies (integerp n) ;drop? maybe can't..
           (equal (logtail (* 8 n) (wintlist byte-list))
                  (wintlist (nthcdr n byte-list))))
  :hints (("Goal" :induct (cdr-and-sub1-induct byte-list n)
           :expand (wintlist byte-list)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable wintlist nthcdr))))

;; ;We probably don't usually want this reduction; rather we usually want to use
;; ;facts about ads1 and ads2 being disjoint or the same (or perhaps obeying a
;; ;subbagp relation).
;; (thm
;;  (equal (wr-list ads1 vals1 (wr-list ads2 vals2 ram))
;;         (wr-list (append ads1 ads2) (append vals1 vals2) ram))
;;  :hints (("Goal" ;:induct (wr-list ads1 vals1 ram)
;;           :in-theory (enable wr-list))))


;bzo
(defthm enlistw4-of-logext
  (equal (enlistw 4 (logext 32 x))
         (enlistw 4 x)))

(defthm loghead-times-8-of-wintlist
  (implies (integerp numbytes)
           (equal (loghead (* 8 numbytes) (wintlist byte-list))
                  (wintlist (firstn numbytes byte-list))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable wintlist firstn))))

(defthm wfixedlist-of-repeat
  (equal (wfixedlist (repeat size elem))
         (if (zp size)
             t
           (unsigned-byte-p 8 elem)))
  :hints (("Goal" :in-theory (enable wfixedlist repeat))))

(defthm wintlist-of-repeat-zero
  (equal (wintlist (repeat size 0))
         0)
  :hints (("Goal" :in-theory (enable wintlist repeat))))





(defthm wfixedlist-of-firstn
  (implies (wfixedlist x)
           (wfixedlist (firstn n x)))
  :hints (("Goal" :in-theory (enable wfixedlist firstn))))

;might loop with the rule use to prove it??
(defthm wintlist-of-firstn
  (implies (and ; (<= 0 n) ;drop?
            (integerp n))
           (equal (wintlist (firstn n x))
                  (loghead (* n 8) (wintlist x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable WINTLIST FIRSTN))))

(defthm firstn-of-enlistw-case-1
  (implies (and (<= n m)
                (integerp m))
           (equal (firstn n (enlistw m val))
                  (enlistw n val))))

;drop if we change enlistw?
(defthm unsigned-byte-p-list-8-of-enlistw
  (unsigned-byte-p-list 8 (enlistw num val))
  :hints (("Goal" :in-theory (enable enlistw
                                     unsigned-byte-p-list))))

(defthmd wintlist-of-nthcdr ;bzo may loop with the rule used to prove it
  (implies (natp n)
           (equal (gacc::wintlist (nthcdr n lst))
                  (logtail (* 8 n) (gacc::wintlist lst))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::wintlist nthcdr))))

(defthm nthcdr-of-enlistw
  (implies (and (natp n)
                (natp size))
           (equal (nthcdr n (gacc::enlistw size val))
                  (gacc::enlistw (- size n) (logtail (* 8 n) val))))
  :hints (("Goal" :in-theory (enable wintlist-of-nthcdr))))

(defthm wintlist-of-append
  (equal (gacc::wintlist (append x y))
         (logapp (* 8 (len x)) (gacc::wintlist x) (gacc::wintlist y))))

(defthm append-of-enlistw-and-enlistw
  (implies (and (equal (* 8 n) m)
                (natp n)
                (natp mm)
                (natp m)
;                (<= n mm)
                )
           (equal (append (gacc::enlistw n val)
                          (gacc::enlistw mm (logtail m val)))
                  (gacc::enlistw (+ mm n) val))))

(defthm memberp-of-logapp-list
  (implies (and (integerp val)
                (natp n))
           (equal (memberp val (gacc::logapp-list n lst val2))
                  (and (memberp (acl2::loghead n val) (gacc::loghead-list n lst))
                       (equal (acl2::logtail n val)
                              (ifix val2)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct t
           :in-theory (enable gacc::logapp-list ACL2::EQUAL-LOGAPP-X-Y-Z))))

;bzo use quantify and make sure it gets this?
;improve the proof? prove it for arbitrary subbag?
(defthm unsigned-byte-p-list-of-remove-1
  (implies (gacc::unsigned-byte-p-list n x)
           (gacc::unsigned-byte-p-list n (bag::remove-1 a x)))
  :hints (("Goal" :in-theory (enable gacc::unsigned-byte-p-list bag::remove-1))))

(defthm unsigned-byte-p-list-implies-integer-listp
  (implies (gacc::unsigned-byte-p-list n lst) ;n is a free var
           (equal (integer-listp lst)
                  (true-listp lst))))

;bzo i don't like how integer-listp also tests for true-listp!
;use this one instead?
(DEFUN INTEGER-LISTP-better (ACL2::L)
  (DECLARE (XARGS :GUARD T))
  (COND ((ATOM ACL2::L)
         t)
        (T (AND (INTEGERP (CAR ACL2::L))
                (INTEGER-LISTP-better (CDR ACL2::L))))))

(DEFTHM GACC::IFIX-LIST-DOES-NOTHING-better
  (IMPLIES (INTEGER-LISTP-better GACC::VALS)
           (EQUAL (GACC::IFIX-LIST GACC::VALS)
                  GACC::VALS))
  :hints (("Goal" :in-theory (enable GACC::IFIX-LIST))))

(defthm unsigned-byte-p-list-implies-integer-listp-better
  (implies (gacc::unsigned-byte-p-list n lst) ;n is a free var
           (integer-listp-better lst))
  :hints (("Goal" :expand ((INTEGER-LISTP-BETTER LST)))))

;more generally wintlist of a usb8 list?
(defthm wintlist-of-loghead-list
  (equal (gacc::wintlist (gacc::loghead-list 8 lst))
         (gacc::wintlist lst)))

(defthm logapp-list-of-fix
  (equal (gacc::logapp-list 16 (list::fix x) j)
         (gacc::logapp-list 16 x j))
  :hints (("Goal" :in-theory (enable gacc::logapp-list))))



;; (thm
;;  (implies (and (true-listp x)
;;                (true-listp y))
;;           (equal (equal x (bag::remove-1 a y))
;;                  (and
;;                   (if (list::memberp a y)
;;                       (bag::perm (cons a x) y)
;;                     (equal x y))))))

(defthm logapp-list-of-remove-1-perm
  (implies (and (bag::unique x) ;allows us to conclude equal instead of perm?
                (acl2::unsigned-byte-p 16 a)
                (gacc::unsigned-byte-p-list 16 x)
                )
           (equal (gacc::logapp-list 16 (bag::remove-1 a x) j)
                  (gacc::remove-1 (acl2::logapp 16 a j)
                                  (gacc::logapp-list 16 x j))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::logapp-list bag::remove-1))))

(local
 (defun 2-list-induct (l1 l2)
   (if (endp l1)
       (list l1 l2)
     (2-list-induct (cdr l1) (bag::remove-1 (car l1) l2)))))

;make  both an make the fw and back local
(defthm gacc::subbagp-of-two-logapp-list-calls-back
  (implies (and (bag::subbagp (gacc::logapp-list 16 vals1 j)
                              (gacc::logapp-list 16 vals2 j))
                (gacc::unsigned-byte-p-list 16 vals1)
                (gacc::unsigned-byte-p-list 16 vals2)
                (bag::unique vals2) ;okay?
                )
           (bag::subbagp vals1 vals2))
  :hints (("Goal" :induct (2-list-induct vals1 vals2)
           :expand (GACC::LOGAPP-LIST 16 VALS1 J)
           :do-not '(generalize eliminate-destructors))))

(defthm gacc::subbagp-of-two-logapp-list-calls-both
  (implies (and (gacc::unsigned-byte-p-list 16 vals1)
                (gacc::unsigned-byte-p-list 16 vals2)
                (bag::unique vals2) ;okay?
                (true-listp vals1)
                (true-listp vals2)
                )
           (equal (bag::subbagp (gacc::logapp-list 16 vals1 j)
                                (gacc::logapp-list 16 vals2 j))
                  (bag::subbagp vals1 vals2))))

(defthm find-index-of-logapp-list
  (implies (and (equal (acl2::logtail 16 val) val2) ;handle the other case?
                (integerp val)
                (acl2::integer-listp lst))
           (equal (list::find-index val (gacc::logapp-list 16 lst val2))
                  (list::find-index (acl2::loghead 16 val) (gacc::loghead-list 16 lst))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::logapp-list
                              (:definition list::find-index)
                              ))))
