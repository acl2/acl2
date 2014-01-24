; Centaur Miscellaneous Books
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/misc/arith-equivs" :dir :system)
(include-book "centaur/misc/absstobjs" :dir :system)
(include-book "std/basic/defs" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable nth update-nth nfix)))
(local (in-theory (enable* arith-equiv-forwarding)))

;; Index function theorems.
(defsection 2darr-index
  (defund-inline 2darr-index (row col nrows ncols)
    (declare (type (integer 0 *) row)
             (type (integer 0 *) col)
             (type (integer 0 *) ncols)
             (type (integer 0 *) nrows)
             (xargs :guard (and (< col ncols)
                                (< row nrows)
                                (< (* nrows ncols) (expt 2 60)))
                    :guard-hints ((and stable-under-simplificationp
                                       '(:nonlinearp t))))
             (ignore nrows))
    (the (unsigned-byte 60)
      (+ (the (unsigned-byte 60) (lnfix col))
         (the (unsigned-byte 60) (* (the (unsigned-byte 60)
                                      (lnfix ncols))
                                    (the (unsigned-byte 60)
                                      (lnfix row)))))))

  (local (in-theory (enable 2darr-index)))

  (defthm natp-2darr-index
    (natp (2darr-index row col nrows ncols))
    :rule-classes :type-prescription)

  (defcong nat-equiv equal (2darr-index row col nrows ncols) 1)
  (defcong nat-equiv equal (2darr-index row col nrows ncols) 2)
  (defcong nat-equiv equal (2darr-index row col nrows ncols) 3)
  (defcong nat-equiv equal (2darr-index row col nrows ncols) 4)

  (defthmd 2darr-index-normalize-nrows
    (implies (syntaxp (not (equal nrows ''0)))
             (equal (2darr-index row col nrows ncols)
                    (2darr-index row col 0 ncols))))

  (defthm 2darr-index-in-bounds
    (implies (and (< (nfix row) (nfix nrows))
                  (< (nfix col) (nfix ncols)))
             (< (2darr-index row col nrows ncols)
                (* (nfix nrows) (nfix ncols))))
    :hints(("Goal" :in-theory (enable 2darr-index))
           (and stable-under-simplificationp
                '(:nonlinearp t)))
    :rule-classes :linear)

  (defthm 2darr-indices-same
    (implies (and (< (nfix col1) (nfix ncols))
                  (< (nfix col2) (nfix ncols)))
             (equal (equal (2darr-index row1 col1 nrows ncols)
                           (2darr-index row2 col2 nrows ncols))
                    (and (equal (nfix row1) (nfix row2))
                         (equal (nfix col1) (nfix col2)))))
    :hints(("Goal" :in-theory (e/d (2darr-index))
            :cases ((< (nfix row1) (nfix row2))
                    (< (nfix row2) (nfix row1))))
           (and stable-under-simplificationp
                '(:nonlinearp t))))

  (defthm 2darr-index-less-than-product
    (implies (natp nrows)
             (and (implies (and (natp ncols)
                                (< (nfix col) ncols))
                           (and (equal (< (2darr-index row col nrows1 ncols) (* nrows ncols))
                                       (< (nfix row) nrows))
                                (equal (< (2darr-index row col nrows1 ncols) (* ncols nrows))
                                       (< (nfix row) nrows))))
                  (implies (< (nfix col) (nfix ncols))
                           (and (equal (< (2darr-index row col nrows1 ncols) (* nrows (nfix ncols)))
                                       (< (nfix row) nrows))
                                (equal (< (2darr-index row col nrows1 ncols) (* (nfix ncols) nrows))
                                       (< (nfix row) nrows))))))
    :hints (("goal" :cases ((< (nfix row) nrows)))
            (and stable-under-simplificationp
                 '(:nonlinearp t)))))

(def-ruleset 2d-arr-base-theory
  (let ((world (w state)))
    (current-theory :here)))





(defun def2darr-events ()
  '(defsection _stobj-name_
     (local (in-theory (enable* 2d-arr-base-theory)))
     (local (include-book "data-structures/list-defthms" :dir :system))
; (local (include-book "arithmetic/top-with-meta" :dir :system))
     (local (include-book "centaur/misc/arith-equivs" :dir :system))
     (local (in-theory (e/d* (nth-of-resize-list-split
                              arith-equiv-forwarding)
                             (nth-with-large-index
                              len-update-nth
                              nth update-nth
                              ))))

     (defstobj _prefix_e-arr2
       (_prefix_e-nrows :type (unsigned-byte 60) :initially 0)
       (_prefix_e-ncols  :type (unsigned-byte 60) :initially 0)
       (_prefix_e-data :type (array _elt-type_ (0))
                       :initially _default-elt_
                       :resizable t)
       :inline t)

     (make-event
      (if (eq '_elt-typep_ 'true-predicate)
          '(value-triple :skipped)
        '(local
          (defthm elt-type-of-nth-of-_prefix_e-datap
            (implies (and (_prefix_e-datap x)
                          (< (nfix n) (len x)))
                     (_elt-typep_ (nth n x)))
            :hints(("Goal" :in-theory (enable nth)))))))

     (make-event
      (if (eq '_elt-fix_ 'id-macro)
          '(value-triple :skipped)
        '(local
          (defthm _prefix_-fix-when-elt-typep
            (implies (_elt-typep_ x)
                     (equal (_elt-fix_ x) x))))))

     (defun _prefix_e-arr2-wfp (_prefix_e-arr2)
       (declare (xargs :stobjs _prefix_e-arr2))
       (and (int= (* (lnfix (_prefix_e-nrows _prefix_e-arr2))
                     (lnfix (_prefix_e-ncols _prefix_e-arr2)))
                  (_prefix_e-data-length _prefix_e-arr2))
            (<= (* (lnfix (_prefix_e-nrows _prefix_e-arr2))
                   (lnfix (_prefix_e-ncols _prefix_e-arr2)))
                (1- (expt 2 60)))))

     (defun-inline _prefix_e-index (row col _prefix_e-arr2)
       (declare (type (integer 0 *) row)
                (type (integer 0 *) col)
                (xargs :stobjs _prefix_e-arr2
                       :guard (and (_prefix_e-arr2-wfp _prefix_e-arr2)
                                   (< row (_prefix_e-nrows _prefix_e-arr2))
                                   (< col (_prefix_e-ncols _prefix_e-arr2)))))
       (2darr-index row col (_prefix_e-nrows _prefix_e-arr2) (_prefix_e-ncols _prefix_e-arr2)))


     (defun-inline _prefix_e-get2 (row col _prefix_e-arr2)
       (declare (type (integer 0 *) row)
                (type (integer 0 *) col)
                (xargs :stobjs _prefix_e-arr2
                       :guard (and (_prefix_e-arr2-wfp _prefix_e-arr2)
                                   (< row (_prefix_e-nrows _prefix_e-arr2))
                                   (< col (_prefix_e-ncols _prefix_e-arr2)))))
       (let ((elt (_prefix_e-datai (_prefix_e-index row col _prefix_e-arr2) _prefix_e-arr2)))
         (mbe :logic (_elt-fix_ elt) :exec elt)))

     (defsection _prefix_e-set2
       (defund-inline _prefix_e-set2 (row col val _prefix_e-arr2)
         (declare (type (integer 0 *) row)
                  (type (integer 0 *) col)
                  (type _elt-type_ val)
                  (xargs :stobjs _prefix_e-arr2
                         :guard (and (_prefix_e-arr2-wfp _prefix_e-arr2)
                                     (< row (_prefix_e-nrows _prefix_e-arr2))
                                     (< col (_prefix_e-ncols _prefix_e-arr2)))))
         (update-_prefix_e-datai (_prefix_e-index row col _prefix_e-arr2) val _prefix_e-arr2))

       (local (in-theory (enable _prefix_e-set2)))

       (defthm _prefix_e-get2-of-_prefix_e-set2
         (implies (and (< (nfix col1) (nfix (_prefix_e-ncols _prefix_e-arr2)))
                       (< (nfix col2) (nfix (_prefix_e-ncols _prefix_e-arr2))))
                  (equal (_prefix_e-get2 row1 col1 (_prefix_e-set2 row2 col2 val2 _prefix_e-arr2))
                         (if (and (equal (nfix row1) (nfix row2))
                                  (equal (nfix col1) (nfix col2)))
                             (_elt-fix_ val2)
                           (_prefix_e-get2 row1 col1 _prefix_e-arr2)))))

       (defthm _prefix_e-ncols-of-_prefix_e-set2
         (equal (_prefix_e-ncols (_prefix_e-set2 row col val _prefix_e-arr2))
                (_prefix_e-ncols _prefix_e-arr2)))

       (defthm _prefix_e-nrows-of-_prefix_e-set2
         (equal (_prefix_e-nrows (_prefix_e-set2 row col val _prefix_e-arr2))
                (_prefix_e-nrows _prefix_e-arr2)))

       (defthm _prefix_e-arr2-wfp-of-_prefix_e-set2
         (implies (and (< (nfix row) (nfix (_prefix_e-nrows _prefix_e-arr2)))
                       (< (nfix col) (nfix (_prefix_e-ncols _prefix_e-arr2)))
                       (_prefix_e-arr2-wfp _prefix_e-arr2))
                  (_prefix_e-arr2-wfp (_prefix_e-set2 row col val _prefix_e-arr2)))))

     (defsection _prefix_e-resize
       ;; changes the number of rows, preserving data
       (defund-inline _prefix_e-resize (nrows _prefix_e-arr2)
         (declare (type (integer 0 *) nrows)
                  (xargs :stobjs _prefix_e-arr2
                         :guard (and (<= (* nrows (_prefix_e-ncols _prefix_e-arr2)) (1- (expt 2 60)))
                                     (<= nrows (1- (expt 2 60))))))
         (let* ((_prefix_e-arr2
                 (resize-_prefix_e-data (* (lnfix nrows)
                                           (lnfix (_prefix_e-ncols _prefix_e-arr2)))
                                        _prefix_e-arr2)))
           (update-_prefix_e-nrows (lnfix nrows) _prefix_e-arr2)))

       (local (in-theory (enable _prefix_e-resize)))

       (defthm _prefix_e-arr2-wfp-of-_prefix_e-resize
         (implies (<= (* (nfix nrows)
                         (nfix (_prefix_e-ncols _prefix_e-arr2))) (1- (expt 2 60)))
                  (_prefix_e-arr2-wfp (_prefix_e-resize nrows _prefix_e-arr2))))

       (defthm _prefix_e-get2-of-_prefix_e-resize
         (implies (and (< (nfix col) (nfix (_prefix_e-ncols _prefix_e-arr2)))
                       (_prefix_e-arr2-wfp _prefix_e-arr2))
                  (equal (_prefix_e-get2 row col (_prefix_e-resize nrows _prefix_e-arr2))
                         (if (< (nfix row) (nfix nrows))
                             (_prefix_e-get2 row col _prefix_e-arr2)
                           _default-elt_)))
         :hints(("Goal" :in-theory (enable nth-with-large-index
                                           2darr-index-normalize-nrows))))

       (defthm _prefix_e-ncols-of-_prefix_e-resize
         (equal (_prefix_e-ncols (_prefix_e-resize nrows _prefix_e-arr2))
                (_prefix_e-ncols _prefix_e-arr2)))

       (defthm _prefix_e-nrows-of-_prefix_e-resize
         (equal (_prefix_e-nrows (_prefix_e-resize nrows _prefix_e-arr2))
                (nfix nrows))))

     (defsection _prefix_e-set-width

       ;; changes the number of columns, deleting data
       (defund-inline _prefix_e-set-width (ncols _prefix_e-arr2)
         (declare (type (integer 0 *) ncols)
                  (xargs :stobjs _prefix_e-arr2
                         :guard (and (<= ncols (1- (expt 2 60)))
                                     (<= (* ncols (_prefix_e-nrows _prefix_e-arr2))
                                         (1- (expt 2 60))))))
         (let* ((_prefix_e-arr2 ;; first delete data
                 (resize-_prefix_e-data 0 _prefix_e-arr2))
                (_prefix_e-arr2 ;; change number of columns
                 (update-_prefix_e-ncols (lnfix ncols) _prefix_e-arr2)))
           (_prefix_e-resize (_prefix_e-nrows _prefix_e-arr2) _prefix_e-arr2)))

       (local (in-theory (enable _prefix_e-set-width)))

       (defthm _prefix_e-arr2-wfp-of-_prefix_e-set-width
         (implies (<= (* (nfix (_prefix_e-nrows _prefix_e-arr2))
                         (nfix ncols))
                      (1- (expt 2 60)))
                  (_prefix_e-arr2-wfp (_prefix_e-set-width ncols _prefix_e-arr2)))
         :hints(("Goal" :in-theory (e/d ()
                                        (_prefix_e-arr2-wfp)))))

       (defthm _prefix_e-get2-of-_prefix_e-set-width
         (equal (_prefix_e-get2 row col (_prefix_e-set-width ncols _prefix_e-arr2))
                _default-elt_)
         :hints(("Goal" :in-theory (enable _prefix_e-resize))))

       (defthm _prefix_e-nrows-of-_prefix_e-set-width
         (equal (_prefix_e-nrows (_prefix_e-set-width ncols _prefix_e-arr2))
                (nfix (_prefix_e-nrows _prefix_e-arr2)))
         :hints(("Goal" :in-theory (disable _prefix_e-nrows))
                (and stable-under-simplificationp
                     '(:in-theory (enable _prefix_e-nrows)))))

       (defthm _prefix_e-ncols-of-_prefix_e-set-width
         (equal (_prefix_e-ncols (_prefix_e-set-width ncols _prefix_e-arr2))
                (nfix ncols))
         :hints(("Goal" :in-theory (disable _prefix_e-ncols))
                (and stable-under-simplificationp
                     '(:in-theory (enable _prefix_e-ncols))))))

     (in-theory (disable _prefix_e-get2 _prefix_e-nrows _prefix_e-ncols
                         _prefix_e-arr2-wfp))

     (defun _prefix_l-arr2-data-wfp (x width)
       (declare (xargs :guard (natp width)))
       (if (atom x)
           (eq x nil)
         (and (_prefix_e-datap (car x))
              (int= (length (car x)) (lnfix width))
              (_prefix_l-arr2-data-wfp (cdr x) width))))

     (defthm true-listp-_prefix_e-data
       (implies (_prefix_e-datap x)
                (true-listp x))
       :rule-classes :forward-chaining)

     (defthm true-listp-_prefix_l-data
       (implies (_prefix_l-arr2-data-wfp x width)
                (true-listp x))
       :rule-classes :forward-chaining)

     (defthm true-listp-nth-of-_prefix_l-data
       (implies (_prefix_l-arr2-data-wfp x width)
                (true-listp (nth n x)))
       :hints(("Goal" :in-theory (enable nth))))

     (defthm _prefix_e-datap-nth-of-_prefix_l-data
       (implies (_prefix_l-arr2-data-wfp x width)
                (_prefix_e-datap (nth n x)))
       :hints(("Goal" :in-theory (enable nth))))

     (defthm len-nth-of-_prefix_l-data
       (implies (and (_prefix_l-arr2-data-wfp x width)
                     (< (nfix n) (len x)))
                (equal (len (nth n x)) (nfix width)))
       :hints(("Goal" :in-theory (enable nth))))

     (local (defthm _prefix_e-datap-of-make-list-ac
              (implies (and (_prefix_e-datap acc)
                            (_elt-typep_ elt))
                       (_prefix_e-datap (make-list-ac size elt acc)))))

     (defun _prefix_l-arr2-wfp (_prefix_l-arr2)
       (declare (Xargs :guard t))
       (and (consp _prefix_l-arr2)
            (natp (car _prefix_l-arr2))
            (_prefix_l-arr2-data-wfp (cdr _prefix_l-arr2) (car _prefix_l-arr2))
            (<= (* (car _prefix_l-arr2) (len (cdr _prefix_l-arr2))) (1- (expt 2 60)))))

     (defun _prefix_l-nrows (_prefix_l-arr2)
       (declare (xargs :guard (_prefix_l-arr2-wfp _prefix_l-arr2)))
       (len (cdr _prefix_l-arr2)))

     (defun _prefix_l-ncols (_prefix_l-arr2)
       (declare (xargs :guard (_prefix_l-arr2-wfp _prefix_l-arr2)))
       (lnfix (car _prefix_l-arr2)))

     (defun _prefix_l-get2 (row col _prefix_l-arr2)
       (declare (type (integer 0 *) row)
                (type (integer 0 *) col)
                (xargs :guard (and (_prefix_l-arr2-wfp _prefix_l-arr2)
                                   (< row (_prefix_l-nrows _prefix_l-arr2))
                                   (< col (_prefix_l-ncols _prefix_l-arr2)))))
       (_elt-fix_ (nth col (nth row (cdr _prefix_l-arr2)))))

     (defsection _prefix_l-set2
       (defund _prefix_l-set2 (row col val _prefix_l-arr2)
         (declare (type (integer 0 *) row)
                  (type (integer 0 *) col)
                  (type _elt-type_ val)
                  (xargs :guard (and (_prefix_l-arr2-wfp _prefix_l-arr2)
                                     (< row (_prefix_l-nrows _prefix_l-arr2))
                                     (< col (_prefix_l-ncols _prefix_l-arr2)))))
         (cons (car _prefix_l-arr2)
               (update-nth row
                           (update-nth col val (nth row (cdr _prefix_l-arr2)))
                           (cdr _prefix_l-arr2))))

       (local (in-theory (enable _prefix_l-set2)))

       (defthm _prefix_l-get2-of-_prefix_l-set2
         (implies (and (< (nfix col1) (nfix (_prefix_l-ncols _prefix_l-arr2)))
                       (< (nfix col2) (nfix (_prefix_l-ncols _prefix_l-arr2))))
                  (equal (_prefix_l-get2 row1 col1 (_prefix_l-set2 row2 col2 val2 _prefix_l-arr2))
                         (if (and (equal (nfix row1) (nfix row2))
                                  (equal (nfix col1) (nfix col2)))
                             (_elt-fix_ val2)
                           (_prefix_l-get2 row1 col1 _prefix_l-arr2)))))

       (defthm _prefix_l-ncols-of-_prefix_l-set2
         (equal (_prefix_l-ncols (_prefix_l-set2 row col val _prefix_l-arr2))
                (_prefix_l-ncols _prefix_l-arr2)))

       (defthm _prefix_l-nrows-of-_prefix_l-set2
         (implies (< (nfix row) (_prefix_l-nrows _prefix_l-arr2))
                  (equal (_prefix_l-nrows (_prefix_l-set2 row col val _prefix_l-arr2))
                         (_prefix_l-nrows _prefix_l-arr2))))

       (local (defthm _prefix_e-datap-of-update-nth
                (implies (and (_prefix_e-datap x)
                              (< (nfix n) (len x))
                              (_elt-typep_ val))
                         (_prefix_e-datap (update-nth n val x)))
                :hints(("Goal" :in-theory (enable update-nth)))))

       (local (defthm _prefix_l-arr2-data-wfp-of-update-nth
                (implies (and (_prefix_l-arr2-data-wfp x width)
                              (< (nfix n) (len x))
                              (_prefix_e-datap val)
                              (equal (len val) (nfix width)))
                         (_prefix_l-arr2-data-wfp (update-nth n val x) width))
                :hints(("Goal" :in-theory (enable update-nth)))))

       (defthm _prefix_l-arr2-wfp-of-_prefix_l-set2
         (implies (and (< (nfix row) (nfix (_prefix_l-nrows _prefix_l-arr2)))
                       (< (nfix col) (nfix (_prefix_l-ncols _prefix_l-arr2)))
                       (_elt-typep_ val)
                       (_prefix_l-arr2-wfp _prefix_l-arr2))
                  (_prefix_l-arr2-wfp (_prefix_l-set2 row col val _prefix_l-arr2)))))

     (defsection _prefix_l-resize
       ;; changes the number of rows, preserving data
       (defund _prefix_l-resize (nrows _prefix_l-arr2)
         (declare (type (integer 0 *) nrows)
                  (xargs :guard (and (_prefix_l-arr2-wfp _prefix_l-arr2)
                                     (<= nrows (1- (expt 2 60)))
                                     (<= (* nrows (_prefix_l-ncols _prefix_l-arr2))
                                         (1- (expt 2 60))))))
         (cons (car _prefix_l-arr2)
               (resize-list (cdr _prefix_l-arr2)
                            (nfix nrows)
                            (make-list (_prefix_l-ncols _prefix_l-arr2)
                                       :initial-element _default-elt_))))

       (local (in-theory (enable _prefix_l-resize)))

       (local
        (defthm _prefix_l-arr2-data-wfp-of-resize-list
          (implies (and (_prefix_l-arr2-data-wfp x width)
                        (_prefix_e-datap elt)
                        (equal (len elt) (nfix width)))
                   (_prefix_l-arr2-data-wfp (resize-list x size elt) width))))

       (defthm _prefix_l-arr2-wfp-of-_prefix_l-resize
         (implies (and (_prefix_l-arr2-wfp _prefix_l-arr2)
                       (<= (* (nfix nrows)
                              (nfix (_prefix_l-ncols _prefix_l-arr2))) (1- (expt 2 60))))
                  (_prefix_l-arr2-wfp (_prefix_l-resize nrows _prefix_l-arr2))))


       (defthm _prefix_l-get2-of-_prefix_l-resize
         (implies (and (< (nfix col) (nfix (_prefix_l-ncols _prefix_l-arr2)))
                       (_prefix_l-arr2-wfp _prefix_l-arr2))
                  (equal (_prefix_l-get2 row col (_prefix_l-resize nrows _prefix_l-arr2))
                         (if (< (nfix row) (nfix nrows))
                             (_prefix_l-get2 row col _prefix_l-arr2)
                           _default-elt_)))
         :hints(("Goal" :in-theory (enable 2darr-index-normalize-nrows
                                           nth-with-large-index))))

       (defthm _prefix_l-ncols-of-_prefix_l-resize
         (equal (_prefix_l-ncols (_prefix_l-resize nrows _prefix_l-arr2))
                (_prefix_l-ncols _prefix_l-arr2)))

       (defthm _prefix_l-nrows-of-_prefix_l-resize
         (equal (_prefix_l-nrows (_prefix_l-resize nrows _prefix_l-arr2))
                (nfix nrows))))

     (defsection _prefix_l-set-width

       ;; changes the number of columns, deleting data
       (defund _prefix_l-set-width (ncols _prefix_l-arr2)
         (declare (type (integer 0 *) ncols)
                  (xargs :guard (and (_prefix_l-arr2-wfp _prefix_l-arr2)
                                     (<= ncols (1- (expt 2 60)))
                                     (<= (* ncols (_prefix_l-nrows _prefix_l-arr2))
                                         (1- (expt 2 60))))))
         (let ((nrows (_prefix_l-nrows _prefix_l-arr2)))
           (cons (nfix ncols)
                 (make-list nrows
                            :initial-element
                            (make-list (nfix ncols) :initial-element _default-elt_)))))

       (local (in-theory (enable _prefix_l-set-width)))

       (local (defthm _prefix_l-arr2-data-wfp-of-make-list-ac
                (implies (and (_prefix_l-arr2-data-wfp acc width)
                              (_prefix_e-datap elt)
                              (equal (len elt) (nfix width)))
                         (_prefix_l-arr2-data-wfp (make-list-ac size elt acc) width))))

       (defthm _prefix_l-arr2-wfp-of-_prefix_l-set-width
         (implies (<= (* (nfix (_prefix_l-nrows _prefix_l-arr2))
                         (nfix ncols))
                      (1- (expt 2 60)))
                  (_prefix_l-arr2-wfp (_prefix_l-set-width ncols _prefix_l-arr2)))
         :hints(("Goal" :in-theory (e/d (_prefix_l-arr2-wfp)
                                        ()))))

       (defthm _prefix_l-get2-of-_prefix_l-set-width
         (equal (_prefix_l-get2 row col (_prefix_l-set-width ncols _prefix_l-arr2))
                _default-elt_)
         :hints(("Goal" :in-theory (enable _prefix_l-resize
                                           nth-with-large-index))))

       (defthm _prefix_l-nrows-of-_prefix_l-set-width
         (equal (_prefix_l-nrows (_prefix_l-set-width ncols _prefix_l-arr2))
                (nfix (_prefix_l-nrows _prefix_l-arr2)))
         :hints(("Goal" :in-theory (disable _prefix_l-nrows))
                (and stable-under-simplificationp
                     '(:in-theory (enable _prefix_l-nrows)))))

       (defthm _prefix_l-ncols-of-_prefix_l-set-width
         (equal (_prefix_l-ncols (_prefix_l-set-width ncols _prefix_l-arr2))
                (nfix ncols))
         :hints(("Goal" :in-theory (disable _prefix_l-ncols))
                (and stable-under-simplificationp
                     '(:in-theory (enable _prefix_l-ncols))))))

     (defsection create-_prefix_l-arr2
       (defun create-_prefix_l-arr2 ()
         (declare (xargs :guard t))
         (list 0)))

     (defun-sk _stobj-name_-lookups-corr (_prefix_e-arr2 _prefix_l-arr2)
       (forall (row col)
               (implies (and ; (< (nfix row) (nfix (_prefix_e-nrows _prefix_e-arr2)))
                         (< (nfix col) (nfix (_prefix_e-ncols _prefix_e-arr2))))
                        (equal (_prefix_e-get2 row col _prefix_e-arr2)
                               (_prefix_l-get2 row col _prefix_l-arr2))))
       :rewrite :direct)

     (defthm _stobj-name_-lookups-corr-expand
       (implies (rewriting-positive-literal `(_stobj-name_-lookups-corr ,_prefix_e-arr2 ,_prefix_l-arr2))
                (equal (_stobj-name_-lookups-corr _prefix_e-arr2 _prefix_l-arr2)
                       (LET ((MV (_STOBJ-NAME_-LOOKUPS-CORR-WITNESS _PREFIX_E-ARR2 _PREFIX_L-ARR2)))
                            (LET ((ROW (MV-NTH 0 MV))
                                  (COL (MV-NTH 1 MV)))
                                 (IMPLIES (AND ;; (< (NFIX ROW)
                                           ;;    (NFIX (_PREFIX_E-NROWS _PREFIX_E-ARR2)))
                                           (< (NFIX COL)
                                              (NFIX (_PREFIX_E-NCOLS _PREFIX_E-ARR2))))
                                          (EQUAL (_PREFIX_E-GET2 ROW COL _PREFIX_E-ARR2)
                                                 (_PREFIX_L-GET2 ROW COL _PREFIX_L-ARR2))))))))

     (in-theory (disable _stobj-name_-lookups-corr))

     (defun-nx _stobj-name_-corr (_prefix_e-arr2 _prefix_l-arr2)
       (and (_prefix_e-arr2-wfp _prefix_e-arr2)
            (equal (_prefix_e-nrows _prefix_e-arr2) (_prefix_l-nrows _prefix_l-arr2))
            (equal (_prefix_e-ncols _prefix_e-arr2) (_prefix_l-ncols _prefix_l-arr2))
            (_stobj-name_-lookups-corr _prefix_e-arr2 _prefix_l-arr2)))

     (in-theory (disable (_stobj-name_-corr)))

     (local (in-theory (disable _prefix_l-get2 _prefix_l-nrows _prefix_l-ncols
                                _prefix_l-arr2-wfp)))


     (defabsstobj-events _stobj-name_
       :concrete _prefix_e-arr2
       :recognizer (_stobj-name_p :logic _prefix_l-arr2-wfp :exec _prefix_e-arr2p)
       :creator (create-_stobj-name_ :logic create-_prefix_l-arr2 :exec create-_prefix_e-arr2)
       :corr-fn _stobj-name_-corr
       :exports ((_prefix_-nrows :logic _prefix_l-nrows :exec _prefix_e-nrows)
                 (_prefix_-ncols :logic _prefix_l-ncols :exec _prefix_e-ncols)
                 (_prefix_-get2 :logic _prefix_l-get2 :exec _prefix_e-get2$inline)
                 (_prefix_-set2$g :logic _prefix_l-set2 :exec _prefix_e-set2$inline)
                 (_prefix_-resize$g :logic _prefix_l-resize :exec _prefix_e-resize$inline
                                    :protect t)
                 (_prefix_-set-width$g :logic _prefix_l-set-width :exec
                                       _prefix_e-set-width$inline
                                       :protect t)))

     (in-theory (enable _prefix_l-arr2-wfp
                        create-_prefix_l-arr2
                        _prefix_l-nrows
                        _prefix_l-ncols
                        _prefix_l-get2
                        _prefix_l-set2
                        _prefix_l-resize
                        _prefix_l-set-width))


     (defun-inline _prefix_-set2 (row col x _stobj-name_)
       (declare (xargs :stobjs _stobj-name_
                       :guard (and (natp row)
                                   (< row (_prefix_-nrows _stobj-name_))
                                   (natp col)
                                   (< col (_prefix_-ncols _stobj-name_))
                                   _elt-guard_)))
       (mbe :logic (_prefix_-set2$g row col x _stobj-name_)
            :exec (if _elt-okp_
                      (_prefix_-set2$g row col x _stobj-name_)
                    (ec-call (_prefix_-set2$g row col x _stobj-name_)))))

     (defun _prefix_-resize (nrows _stobj-name_)
       (declare (xargs :stobjs _stobj-name_
                       :guard (natp nrows)))
       (mbe :logic (_prefix_-resize$g nrows _stobj-name_)
            :exec (if (and (<= (* nrows (_prefix_-ncols _stobj-name_))
                               (1- (expt 2 60)))
                           (<= nrows (1- (expt 2 60))))
                      (_prefix_-resize$g nrows _stobj-name_)
                    (ec-call (_prefix_-resize$g nrows _stobj-name_)))))

     (defun _prefix_-set-width (ncols _stobj-name_)
       (declare (xargs :stobjs _stobj-name_
                       :guard (natp ncols)
                       :guard-debug t))
       (mbe :logic (_prefix_-set-width$g ncols _stobj-name_)
            :exec (if (and (<= (* ncols (_prefix_-nrows _stobj-name_))
                               (1- (expt 2 60)))
                           (<= ncols (1- (expt 2 60))))
                      (_prefix_-set-width$g ncols _stobj-name_)
                    (ec-call (_prefix_-set-width$g ncols _stobj-name_)))))))

(include-book "std/strings/substrp" :dir :system)
(include-book "std/strings/strsubst" :dir :system)

(defun subst-substrs (alist x)
  (declare (xargs :guard (and (alistp alist)
                              (string-listp (strip-cars alist))
                              (string-listp (strip-cdrs alist))
                              (stringp x))))
  (if (atom alist)
      x
    (if (str::substrp (caar alist) x)
        (subst-substrs (cdr alist)
                       (str::strsubst (caar alist) (cdar alist) x))
      (subst-substrs (cdr alist) x))))

(defun sublis-symbol-substrs (alist x pkg)
  (declare (xargs :guard (and (alistp alist)
                              (string-listp (Strip-cars alist))
                              (string-listp (strip-cdrs alist))
                              (symbolp pkg))))
  (if (atom x)
      (if (symbolp x)
          (let* ((name (symbol-name x))
                 (new-name (subst-substrs alist name)))
            (if (equal name new-name)
                x
              (intern-in-package-of-symbol new-name pkg)))
        x)
    (cons (sublis-symbol-substrs alist (car x) pkg)
          (sublis-symbol-substrs alist (cdr x) pkg))))

(defmacro id-macro (x) x)
(defun true-predicate (x)
  (declare (ignore x))
  t)

(defmacro def2darr (stobj-name &key
                               prefix ;; symbol, same as stobj-name by default

                               (elt-type 't) ;; type declaration
                               ;; function/lambda equivalent to type declaration
                               (elt-typep 'true-predicate)

                               default-elt ;; constant

                               ;; function/lambda -- must be idempotent when elt-typep
                               (elt-fix 'id-macro)

                               ;; guard requirement for element -- term in
                               ;; terms of x
                               (elt-guard 't)

                               ;; check element at runtime -- term in terms of
                               ;; x. together with elt-guard must imply elt-typep.
                               (elt-okp 't))
  (let ((symsubst-alist `((_elt-type_ . ,elt-type)
                          (_elt-typep_ . ,elt-typep)
                          (_default-elt_ . ,default-elt)
                          (_elt-fix_ . ,elt-fix)
                          (_elt-guard_ . ,elt-guard)
                          (_elt-okp_ . ,elt-okp)))
        (strsubst-alist `(("_STOBJ-NAME_" . ,(symbol-name stobj-name))
                          ("_PREFIX_" . ,(if prefix
                                             (symbol-name prefix)
                                           (symbol-name stobj-name))))))
    (sublis symsubst-alist
            (sublis-symbol-substrs strsubst-alist
                                   (def2darr-events) stobj-name))))


(local
 (progn
   ;; test

   (defun f-stringp (x)
     (declare (xargs :guard t))
     (and (stringp x)
          (< 0 (length x))
          (eql (char x 0) #\f)))

   (defun nonempty-str-fix (x)
     (declare (xargs :guard t))
     (if (and (stringp x) (< 0 (length x)))
         x
       "f"))

   (defthm f-stringp-when-stringp
     (implies (and (stringp x)
                   (< 0 (length x))
                   (equal (char x 0) #\f))
              (f-stringp x)))

   (defthm nonempty-str-fix-when-f-stringp
     (implies (f-stringp x)
              (equal (nonempty-str-fix x) x)))

   (in-theory (disable f-stringp nonempty-str-fix))

   (def2darr fstring2d :prefix fs2d
     :elt-type (and string (satisfies f-stringp))
     :elt-typep (lambda (x) (and (stringp x) (f-stringp x)))
     :default-elt "f"
     :elt-fix nonempty-str-fix
     :elt-guard (stringp x)
     :elt-okp (and (< 0 (length x)) (eql (char x 0) #\f)))))
