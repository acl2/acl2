; ACL2 Standard Library
; Copyright (C) 2008-2016 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "STOBJS")
(include-book "absstobjs")
(include-book "std/basic/defs" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "std/strings/substrp" :dir :system)
(include-book "std/strings/strsubst" :dir :system)
(include-book "xdoc/str" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (in-theory (disable nth update-nth nfix)))
(local (in-theory (enable* arith-equiv-forwarding)))

(defxdoc def-2d-arr
  :parents (std/stobjs)
  :short "Defines a @(see abstract-stobj) for a two-dimensional array."

  :long "<p>@('Def-2d-arr') produces an @(see abstract-stobj) with associated
@('get2')/@('set2'), @('nrows')/@('ncols'), @('resize-rows')/@('resize-cols')
functions.  Logically the stobj looks like a list of lists.  But for execution,
these functions are stobj array operations that manipulate a (one-dimensional)
stobj array.</p>

<h3>Example</h3>

<p>The following defines a two-dimensional array of integers named
@('intmatrix').</p>

@({
    (def-2d-arr intmatrix         ;; Stobj name
      :prefix      imx            ;; Base name for accessor functions (optional)
      :pred        integerp       ;; Element type recognizer (optional)
      :type-decl   integer        ;; Element type-spec (optional)
      :fix         ifix           ;; Element fixing function (optional)
      :default-val 0              ;; Element default value (for resizing)
      :parents (my-algorithm))    ;; XDOC parent topics
})

<h3>Keyword Options</h3>

<dl>

<dt>@(':prefix')</dt>

<dd>This is used for name generation.  For example, by using @('imx') above, we
will get functions named @('imx-nrows'), @('imx-ncols'), @('imx-resize-rows'),
@('imx-resize-cols'), @('imx-get2'), and @('imx-set2').  If you don't provide a
custom prefix we just use the stobj name.</dd>

<dt>@(':pred')</dt>

<dd>Specifies an element recognizer function. This can be used to restrict the
types of elements that can be put into the array.</dd>

<dt>@(':default-val')</dt>

<dd>This gives the default array element for resizing, i.e., the
@(':initially') argument to the underlying @(see stobj).  This is often
necessary when you provide a restricted @(':pred'), because the default value
needs to satisfy the predicate.</dd>

<dt>@(':type-decl')</dt>

<dd>This provides a Common Lisp @(see acl2::type-spec) declaration for a single
element's type.  It primarily affects memory efficienty and performance.  If
provided, it must sensibly agree with the given @(':pred').</dd>

<dt>@(':fix')</dt>

<dd>Optional, requires a compatible @(':pred').  This alters the logical
definition of the @('get2') function so that it always produces a result of the
correct type.  For instance, by using @(':fix ifix') above, @('imx-get2')
will (logically) return the @(see ifix) of the element at that position in the
array.</dd>

<dt>@(':parents'), @(':short'), @(':long')</dt>

<dd>These options are as in @(see defxdoc).  Note that you typically don't need
to give @(':short') or @(':long') descriptions because reasonable boilerplate
documentation can be generated automatically.</dd>

</dl>

<h3>Advanced/Obscure Options</h3>

<p>In certain cases, you may want to use a stronger @('type-decl') than your
@('pred') really allows.  For instance, you might want Common Lisp to know that
your array really contains fixnums, but logically just imagine that the array
contains arbitrary integers (and hence avoid the difficulty of bounds checking
when using the array).</p>

<p>The options @(':elt-guard'), @(':elt-okp'), and @(':xvar') can be used to
customize the @('set') function to accomplish this.  See for instance @('s61v')
in @('std/stobjs/tests/2d-arr.lisp') for an example.</p>")


(define 2darr-index ((row   :type (integer 0 *))
                     (col   :type (integer 0 *))
                     (nrows :type (integer 0 *))
                     (ncols :type (integer 0 *)))
  :returns (index natp :rule-classes :type-prescription)
  :guard (and (< col ncols)
              (< row nrows)
              (< (* nrows ncols) (expt 2 60)))
  :guard-hints ((and stable-under-simplificationp '(:nonlinearp t)))
  ;; Don't document this, just an implementation detail
  (declare (ignore nrows))
  (the (unsigned-byte 60)
       (+ (the (unsigned-byte 60) (lnfix col))
          (the (unsigned-byte 60) (* (the (unsigned-byte 60) (lnfix ncols))
                                     (the (unsigned-byte 60) (lnfix row))))))
  ///
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


(local (in-theory (disable floor)))

(local (defthm floor-bound
         (implies (and (natp x) (natp y))
                  (<= (* y (floor x y)) x))
         :rule-classes :linear))


(define 2darr-index-inverse ((idx :type (integer 0 *))
                             (nrows :type (integer 0 *))
                             (ncols :type (integer 0 *)))
  :guard (< idx (* ncols nrows))
  (declare (ignore nrows))
  :returns (mv (row-idx natp :rule-classes :type-prescription)
               (col-idx natp :rule-classes :type-prescription))
  (b* ((idx (lnfix idx))
       (ncols (lnfix ncols)))
    (if (eql 0 ncols)
        (mv 0 idx)
      (mv (floor idx ncols)
          (mod idx ncols))))
  ///
  (defthm 2darr-index-inverse-of-2darr-index
    (implies (and (< (nfix row) (nfix nrows))
                  (< (nfix col) (nfix ncols)))
             (equal (2darr-index-inverse (2darr-index row col nrows ncols) nrows ncols)
                    (mv (nfix row) (nfix col))))
    :hints(("Goal" :in-theory (enable 2darr-index))))

  (defthm 2darr-index-of-2darr-index-inverse
    (b* (((mv row col) (2darr-index-inverse idx nrows ncols)))
      (equal (2darr-index row col nrows ncols)
             (nfix idx)))
    :hints(("Goal" :in-theory (enable 2darr-index))))

  (local (defthm nonlinear-lemma
           (implies (and (< x (* y z))
                         (<= z f)
                         (natp x) (natp y) (natp z) (natp f))
                    (< x (* y f)))
           :hints (("goal" :nonlinearp t))))

  (defthm 2darr-index-inverse-in-bounds
    (implies (< (nfix idx) (* (nfix ncols) (nfix nrows)))
             (b* (((mv row col) (2darr-index-inverse idx nrows ncols)))
               (and (< row (nfix nrows))
                    (< col (nfix ncols)))))
    :hints (("goal" :use ((:instance floor-bound (x (nfix idx)) (y ncols)))
             :in-theory (disable floor-bound)))
    :rule-classes :linear))


(def-ruleset! 2d-arr-base-theory
  (let ((world (w state)))
    (current-theory :here)))


(define 2darr-p (x)
  (and (consp x)
       (natp (car x))
       (true-listp (cdr x))))

(define 2darr->ncols ((x 2darr-p))
  :returns (ncols natp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (enable 2darr-p))))
  (lnfix (car x)))

(define 2darr->rows ((x 2darr-p))
  :returns (rows true-listp :rule-classes :type-prescription)
  :prepwork ((local (in-theory (enable 2darr-p))))
  (mbe :logic (acl2::list-fix (cdr x)) :exec (cdr x)))

(define 2darr-fix ((x 2darr-p))
  :returns (new-x 2darr-p)
  :prepwork ((local (in-theory (enable 2darr-p 2darr->ncols 2darr->rows))))
  (mbe :logic (cons (2darr->ncols x)
                    (2darr->rows x))
       :exec x)
  ///
  (defthm 2darr-fix-when-2darr-p
    (implies (2darr-p x)
             (equal (2darr-fix x) x)))

  (defthm 2darr->ncols-of-2darr-fix
    (equal (2darr->ncols (2darr-fix x))
           (2darr->ncols x)))

  (defthm 2darr->rows-of-2darr-fix
    (equal (2darr->rows (2darr-fix x))
           (2darr->rows x))))

(define 2darr ((ncols natp) (rows true-listp))
  :returns (2darr 2darr-p)
  :prepwork ((local (in-theory (enable 2darr->ncols 2darr->rows 2darr-fix 2darr-p))))
  (cons (lnfix ncols)
        (mbe :logic (acl2::list-fix rows) :exec rows))
  ///

  (defthm 2darr-ncols-rows-identity
    (equal (2darr (2darr->ncols x) (2darr->rows x))
           (2darr-fix x)))

  (defthm 2darr->ncols-of-2darr
    (equal (2darr->ncols (2darr ncols rows))
           (nfix ncols)))

  (defthm 2darr->rows-of-2darr
    (equal (2darr->rows (2darr ncols rows))
           (acl2::list-fix rows))))
    

(defun def2darr-events ()
  '(defsection _stobj-name_
     (local (in-theory (enable* 2d-arr-base-theory)))
     (local (include-book "data-structures/list-defthms" :dir :system))

     (local (in-theory (e/d* (acl2::nth-of-resize-list-split
                              arith-equiv-forwarding)
                             (acl2::nth-with-large-index
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
       (declare (xargs :stobjs _prefix_e-arr2
                       :guard (and (_prefix_e-arr2-wfp _prefix_e-arr2)
                                   (natp row)
                                   (natp col)
                                   (< row (_prefix_e-nrows _prefix_e-arr2))
                                   (< col (_prefix_e-ncols _prefix_e-arr2)))
                       :split-types t)
                (type (integer 0 *) row)
                (type (integer 0 *) col))
       (let ((elt (_prefix_e-datai (_prefix_e-index row col _prefix_e-arr2) _prefix_e-arr2)))
         (mbe :logic (_elt-fix_ elt) :exec elt)))

     (defsection _prefix_e-get
       (defund-inline _prefix_e-get (idx _prefix_e-arr2)
         (declare (xargs :stobjs _prefix_e-arr2
                         :guard (and (_prefix_e-arr2-wfp _prefix_e-arr2)
                                     (natp idx)
                                     (< idx (* (_prefix_e-nrows _prefix_e-arr2)
                                               (_prefix_e-ncols _prefix_e-arr2))))
                         :split-types t)
                  (type (integer 0 *) idx))
         (let ((elt (_prefix_e-datai idx _prefix_e-arr2)))
           (mbe :logic (_elt-fix_ elt) :exec elt)))

       (local (in-theory (enable _prefix_e-get)))

       (defthm _prefix_e-get-in-terms-of-_prefix_e-get2
         (equal (_prefix_e-get idx _prefix_e-arr2)
                (b* (((mv row col) (2darr-index-inverse
                                    idx (_prefix_e-nrows _prefix_e-arr2)
                                    (_prefix_e-ncols _prefix_e-arr2))))
                  (_prefix_e-get2 row col _prefix_e-arr2)))))

     (defsection _prefix_e-set2
       (defund-inline _prefix_e-set2 (row col val _prefix_e-arr2)
         (declare (xargs :stobjs _prefix_e-arr2
                         :guard (and (_prefix_e-arr2-wfp _prefix_e-arr2)
                                     (_elt-typep_ val)
                                     (natp row)
                                     (natp col)
                                     (< row (_prefix_e-nrows _prefix_e-arr2))
                                     (< col (_prefix_e-ncols _prefix_e-arr2)))
                         :split-types t)
                  (type (integer 0 *) row col)
                  (type _elt-type_ val))
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
                  (_prefix_e-arr2-wfp (_prefix_e-set2 row col val _prefix_e-arr2))))

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

     (defsection _prefix_e-set
       (defund-inline _prefix_e-set (idx val _prefix_e-arr2)
         (declare (xargs :stobjs _prefix_e-arr2
                         :guard (and (_prefix_e-arr2-wfp _prefix_e-arr2)
                                     (_elt-typep_ val)
                                     (natp idx)
                                     (< idx (* (_prefix_e-nrows _prefix_e-arr2)
                                               (_prefix_e-ncols _prefix_e-arr2))))
                         :split-types t)
                  (type (integer 0 *) idx)
                  (type _elt-type_ val))
         (update-_prefix_e-datai idx val _prefix_e-arr2))

       (local (in-theory (enable _prefix_e-set _prefix_e-set2)))

       (defthm _prefix_e-set-in-terms-of-_prefix_e-set2
         (equal (_prefix_e-set idx val _prefix_e-arr2)
                (b* (((mv row col) (2darr-index-inverse
                                    idx (_prefix_e-nrows _prefix_e-arr2)
                                    (_prefix_e-ncols _prefix_e-arr2))))
                  (_prefix_e-set2 row col val _prefix_e-arr2)))))

     (defsection _prefix_e-resize-rows
       ;; changes the number of rows, preserving data
       (defund-inline _prefix_e-resize-rows (nrows _prefix_e-arr2)
         (declare (type (integer 0 *) nrows)
                  (xargs :stobjs _prefix_e-arr2
                         :guard (and (<= (* nrows (_prefix_e-ncols _prefix_e-arr2)) (1- (expt 2 60)))
                                     (<= nrows (1- (expt 2 60))))))
         (let* ((_prefix_e-arr2
                 (resize-_prefix_e-data (* (lnfix nrows)
                                           (lnfix (_prefix_e-ncols _prefix_e-arr2)))
                                        _prefix_e-arr2)))
           (update-_prefix_e-nrows (lnfix nrows) _prefix_e-arr2)))

       (local (in-theory (enable _prefix_e-resize-rows)))

       (defthm _prefix_e-arr2-wfp-of-_prefix_e-resize-rows
         (implies (<= (* (nfix nrows)
                         (nfix (_prefix_e-ncols _prefix_e-arr2))) (1- (expt 2 60)))
                  (_prefix_e-arr2-wfp (_prefix_e-resize-rows nrows _prefix_e-arr2))))

       (defthm _prefix_e-get2-of-_prefix_e-resize-rows
         (implies (and (< (nfix col) (nfix (_prefix_e-ncols _prefix_e-arr2)))
                       (_prefix_e-arr2-wfp _prefix_e-arr2))
                  (equal (_prefix_e-get2 row col (_prefix_e-resize-rows nrows _prefix_e-arr2))
                         (if (< (nfix row) (nfix nrows))
                             (_prefix_e-get2 row col _prefix_e-arr2)
                           _default-elt_)))
         :hints(("Goal" :in-theory (enable acl2::nth-with-large-index
                                           2darr-index-normalize-nrows))))

       (defthm _prefix_e-ncols-of-_prefix_e-resize-rows
         (equal (_prefix_e-ncols (_prefix_e-resize-rows nrows _prefix_e-arr2))
                (_prefix_e-ncols _prefix_e-arr2)))

       (defthm _prefix_e-nrows-of-_prefix_e-resize-rows
         (equal (_prefix_e-nrows (_prefix_e-resize-rows nrows _prefix_e-arr2))
                (nfix nrows))))

     (defsection _prefix_e-resize-cols

       ;; changes the number of columns, deleting data
       (defund-inline _prefix_e-resize-cols (ncols _prefix_e-arr2)
         (declare (type (integer 0 *) ncols)
                  (xargs :stobjs _prefix_e-arr2
                         :guard (and (<= ncols (1- (expt 2 60)))
                                     (<= (* ncols (_prefix_e-nrows _prefix_e-arr2))
                                         (1- (expt 2 60))))))
         (let* ((_prefix_e-arr2 ;; first delete data
                 (resize-_prefix_e-data 0 _prefix_e-arr2))
                (_prefix_e-arr2 ;; change number of columns
                 (update-_prefix_e-ncols (lnfix ncols) _prefix_e-arr2)))
           (_prefix_e-resize-rows (_prefix_e-nrows _prefix_e-arr2) _prefix_e-arr2)))

       (local (in-theory (enable _prefix_e-resize-cols)))

       (defthm _prefix_e-arr2-wfp-of-_prefix_e-resize-cols
         (implies (<= (* (nfix (_prefix_e-nrows _prefix_e-arr2))
                         (nfix ncols))
                      (1- (expt 2 60)))
                  (_prefix_e-arr2-wfp (_prefix_e-resize-cols ncols _prefix_e-arr2)))
         :hints(("Goal" :in-theory (e/d ()
                                        (_prefix_e-arr2-wfp)))))

       (defthm _prefix_e-get2-of-_prefix_e-resize-cols
         (equal (_prefix_e-get2 row col (_prefix_e-resize-cols ncols _prefix_e-arr2))
                _default-elt_)
         :hints(("Goal" :in-theory (enable _prefix_e-resize-rows))))

       (defthm _prefix_e-nrows-of-_prefix_e-resize-cols
         (equal (_prefix_e-nrows (_prefix_e-resize-cols ncols _prefix_e-arr2))
                (nfix (_prefix_e-nrows _prefix_e-arr2)))
         :hints(("Goal" :in-theory (disable _prefix_e-nrows))
                (and stable-under-simplificationp
                     '(:in-theory (enable _prefix_e-nrows)))))

       (defthm _prefix_e-ncols-of-_prefix_e-resize-cols
         (equal (_prefix_e-ncols (_prefix_e-resize-cols ncols _prefix_e-arr2))
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
       (and (2darr-p _prefix_l-arr2)
            (_prefix_l-arr2-data-wfp (2darr->rows _prefix_l-arr2) (2darr->ncols _prefix_l-arr2))
            (<= (* (2darr->ncols _prefix_l-arr2) (len (2darr->rows _prefix_l-arr2))) (1- (expt 2 60)))))

     (defun _prefix_l-nrows (_prefix_l-arr2)
       (declare (xargs :guard (_prefix_l-arr2-wfp _prefix_l-arr2)))
       (len (2darr->rows _prefix_l-arr2)))

     (defun _prefix_l-ncols (_prefix_l-arr2)
       (declare (xargs :guard (_prefix_l-arr2-wfp _prefix_l-arr2)))
       (2darr->ncols _prefix_l-arr2))

     (defun _prefix_l-get2 (row col _prefix_l-arr2)
       (declare (type (integer 0 *) row)
                (type (integer 0 *) col)
                (xargs :guard (and (_prefix_l-arr2-wfp _prefix_l-arr2)
                                   (< row (_prefix_l-nrows _prefix_l-arr2))
                                   (< col (_prefix_l-ncols _prefix_l-arr2)))))
       (_elt-fix_ (nth col (nth row (2darr->rows _prefix_l-arr2)))))

     (defun _prefix_l-get (idx _prefix_l-arr2)
       (declare (type (integer 0 *) idx)
                (xargs :guard (and (_prefix_l-arr2-wfp _prefix_l-arr2)
                                   (< idx (* (_prefix_l-nrows _prefix_l-arr2)
                                             (_prefix_l-ncols _prefix_l-arr2))))))
       (b* (((mv row col) (2darr-index-inverse idx (_prefix_l-nrows _prefix_l-arr2)
                                             (_prefix_l-ncols _prefix_l-arr2))))
         (_prefix_l-get2 row col _prefix_l-arr2)))

     (defsection _prefix_l-set2
       (defund _prefix_l-set2 (row col val _prefix_l-arr2)
         (declare (type (integer 0 *) row)
                  (type (integer 0 *) col)
                  (type _elt-type_ val)
                  (xargs :guard (and (_prefix_l-arr2-wfp _prefix_l-arr2)
                                     (< row (_prefix_l-nrows _prefix_l-arr2))
                                     (< col (_prefix_l-ncols _prefix_l-arr2)))))
         (2darr (2darr->ncols _prefix_l-arr2)
                (update-nth row
                            (update-nth col val (nth row (2darr->rows _prefix_l-arr2)))
                            (2darr->rows _prefix_l-arr2))))

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

     (defun _prefix_l-set (idx val _prefix_l-arr2)
         (declare (type (integer 0 *) idx)
                  (type _elt-type_ val)
                  (xargs :guard (and (_prefix_l-arr2-wfp _prefix_l-arr2)
                                     (< idx (* (_prefix_l-nrows _prefix_l-arr2)
                                               (_prefix_l-ncols _prefix_l-arr2))))))
         (b* (((mv row col) (2darr-index-inverse idx (_prefix_l-nrows _prefix_l-arr2)
                                               (_prefix_l-ncols _prefix_l-arr2))))
           (_prefix_l-set2 row col val _prefix_l-arr2)))

     (defsection _prefix_l-resize-rows
       ;; changes the number of rows, preserving data
       (defund _prefix_l-resize-rows (nrows _prefix_l-arr2)
         (declare (type (integer 0 *) nrows)
                  (xargs :guard (and (_prefix_l-arr2-wfp _prefix_l-arr2)
                                     (<= nrows (1- (expt 2 60)))
                                     (<= (* nrows (_prefix_l-ncols _prefix_l-arr2))
                                         (1- (expt 2 60))))))
         (2darr (2darr->ncols _prefix_l-arr2)
                (resize-list (2darr->rows _prefix_l-arr2)
                             (nfix nrows)
                             (make-list (_prefix_l-ncols _prefix_l-arr2)
                                        :initial-element _default-elt_))))

       (local (in-theory (enable _prefix_l-resize-rows)))

       (local
        (defthm _prefix_l-arr2-data-wfp-of-resize-list
          (implies (and (_prefix_l-arr2-data-wfp x width)
                        (_prefix_e-datap elt)
                        (equal (len elt) (nfix width)))
                   (_prefix_l-arr2-data-wfp (resize-list x size elt) width))))

       (defthm _prefix_l-arr2-wfp-of-_prefix_l-resize-rows
         (implies (and (_prefix_l-arr2-wfp _prefix_l-arr2)
                       (<= (* (nfix nrows)
                              (nfix (_prefix_l-ncols _prefix_l-arr2))) (1- (expt 2 60))))
                  (_prefix_l-arr2-wfp (_prefix_l-resize-rows nrows _prefix_l-arr2))))


       (defthm _prefix_l-get2-of-_prefix_l-resize-rows
         (implies (and (< (nfix col) (nfix (_prefix_l-ncols _prefix_l-arr2)))
                       (_prefix_l-arr2-wfp _prefix_l-arr2))
                  (equal (_prefix_l-get2 row col (_prefix_l-resize-rows nrows _prefix_l-arr2))
                         (if (< (nfix row) (nfix nrows))
                             (_prefix_l-get2 row col _prefix_l-arr2)
                           _default-elt_)))
         :hints(("Goal" :in-theory (enable 2darr-index-normalize-nrows
                                           acl2::nth-with-large-index))))

       (defthm _prefix_l-ncols-of-_prefix_l-resize-rows
         (equal (_prefix_l-ncols (_prefix_l-resize-rows nrows _prefix_l-arr2))
                (_prefix_l-ncols _prefix_l-arr2)))

       (defthm _prefix_l-nrows-of-_prefix_l-resize-rows
         (equal (_prefix_l-nrows (_prefix_l-resize-rows nrows _prefix_l-arr2))
                (nfix nrows))))

     (defsection _prefix_l-resize-cols

       ;; changes the number of columns, deleting data
       (defund _prefix_l-resize-cols (ncols _prefix_l-arr2)
         (declare (type (integer 0 *) ncols)
                  (xargs :guard (and (_prefix_l-arr2-wfp _prefix_l-arr2)
                                     (<= ncols (1- (expt 2 60)))
                                     (<= (* ncols (_prefix_l-nrows _prefix_l-arr2))
                                         (1- (expt 2 60))))))
         (let ((nrows (_prefix_l-nrows _prefix_l-arr2)))
           (2darr (nfix ncols)
                 (make-list nrows
                            :initial-element
                            (make-list (nfix ncols) :initial-element _default-elt_)))))

       (local (in-theory (enable _prefix_l-resize-cols)))

       (local (defthm _prefix_l-arr2-data-wfp-of-make-list-ac
                (implies (and (_prefix_l-arr2-data-wfp acc width)
                              (_prefix_e-datap elt)
                              (equal (len elt) (nfix width)))
                         (_prefix_l-arr2-data-wfp (make-list-ac size elt acc) width))))

       (defthm _prefix_l-arr2-wfp-of-_prefix_l-resize-cols
         (implies (<= (* (nfix (_prefix_l-nrows _prefix_l-arr2))
                         (nfix ncols))
                      (1- (expt 2 60)))
                  (_prefix_l-arr2-wfp (_prefix_l-resize-cols ncols _prefix_l-arr2)))
         :hints(("Goal" :in-theory (e/d (_prefix_l-arr2-wfp)
                                        ()))))

       (defthm _prefix_l-get2-of-_prefix_l-resize-cols
         (equal (_prefix_l-get2 row col (_prefix_l-resize-cols ncols _prefix_l-arr2))
                _default-elt_)
         :hints(("Goal" :in-theory (enable _prefix_l-resize-rows
                                           acl2::nth-with-large-index))))

       (defthm _prefix_l-nrows-of-_prefix_l-resize-cols
         (equal (_prefix_l-nrows (_prefix_l-resize-cols ncols _prefix_l-arr2))
                (nfix (_prefix_l-nrows _prefix_l-arr2)))
         :hints(("Goal" :in-theory (disable _prefix_l-nrows))
                (and stable-under-simplificationp
                     '(:in-theory (enable _prefix_l-nrows)))))

       (defthm _prefix_l-ncols-of-_prefix_l-resize-cols
         (equal (_prefix_l-ncols (_prefix_l-resize-cols ncols _prefix_l-arr2))
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
       (implies (acl2::rewriting-positive-literal `(_stobj-name_-lookups-corr ,_prefix_e-arr2 ,_prefix_l-arr2))
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
       :foundation _prefix_e-arr2
       :recognizer (_stobj-name_p :logic _prefix_l-arr2-wfp :exec _prefix_e-arr2p)
       :creator (create-_stobj-name_ :logic create-_prefix_l-arr2 :exec create-_prefix_e-arr2)
       :corr-fn _stobj-name_-corr
       :exports ((_prefix_-nrows  :logic _prefix_l-nrows :exec _prefix_e-nrows)
                 (_prefix_-ncols  :logic _prefix_l-ncols :exec _prefix_e-ncols)
                 (_prefix_-get2   :logic _prefix_l-get2  :exec _prefix_e-get2$inline)
                 (_prefix_-get    :logic _prefix_l-get   :exec _prefix_e-get$inline)
                 (_prefix_-set2$g :logic _prefix_l-set2  :exec _prefix_e-set2$inline)
                 (_prefix_-set$g  :logic _prefix_l-set   :exec _prefix_e-set$inline)
                 (_prefix_-resize-rows$g :logic _prefix_l-resize-rows
                                         :exec _prefix_e-resize-rows$inline
                                         :protect t)
                 (_prefix_-resize-cols$g :logic _prefix_l-resize-cols
                                         :exec _prefix_e-resize-cols$inline
                                         :protect t)))

     (in-theory (enable _prefix_l-arr2-wfp
                        create-_prefix_l-arr2
                        _prefix_l-nrows
                        _prefix_l-ncols
                        _prefix_l-get2
                        _prefix_l-set2
                        _prefix_l-resize-rows
                        _prefix_l-resize-cols))

     (defun _prefix_-set2 (row col _xvar_ _stobj-name_)
       (declare (xargs :guard (and (natp row)
                                   (natp col)
                                   (< row (_prefix_-nrows _stobj-name_))
                                   (< col (_prefix_-ncols _stobj-name_))
                                   _elt-guard_)
                       :stobjs _stobj-name_))
       (mbe :logic (_prefix_-set2$g row col _xvar_ _stobj-name_)
            :exec (if _elt-okp_
                      (_prefix_-set2$g row col _xvar_ _stobj-name_)
                    (ec-call (_prefix_-set2$g row col _xvar_ _stobj-name_)))))

     (defun _prefix_-set (idx _xvar_ _stobj-name_)
       (declare (xargs :guard (and (natp idx)
                                   (< idx (* (_prefix_-nrows _stobj-name_)
                                             (_prefix_-ncols _stobj-name_)))
                                   _elt-guard_)
                       :stobjs _stobj-name_))
       (mbe :logic (_prefix_-set$g idx _xvar_ _stobj-name_)
            :exec (if _elt-okp_
                      (_prefix_-set$g idx _xvar_ _stobj-name_)
                    (ec-call (_prefix_-set$g idx _xvar_ _stobj-name_)))))

     (defun _prefix_-resize-rows (nrows _stobj-name_)
       (declare (xargs :stobjs _stobj-name_
                       :guard (natp nrows)))
       (mbe :logic (_prefix_-resize-rows$g nrows _stobj-name_)
            :exec (if (and (<= (* nrows (_prefix_-ncols _stobj-name_))
                               (1- (expt 2 60)))
                           (<= nrows (1- (expt 2 60))))
                      (_prefix_-resize-rows$g nrows _stobj-name_)
                    (ec-call (_prefix_-resize-rows$g nrows _stobj-name_)))))

     (defun _prefix_-resize-cols (ncols _stobj-name_)
       (declare (xargs :stobjs _stobj-name_
                       :guard (natp ncols)
                       :guard-debug t))
       (mbe :logic (_prefix_-resize-cols$g ncols _stobj-name_)
            :exec (if (and (<= (* ncols (_prefix_-nrows _stobj-name_))
                               (1- (expt 2 60)))
                           (<= ncols (1- (expt 2 60))))
                      (_prefix_-resize-cols$g ncols _stobj-name_)
                    (ec-call (_prefix_-resize-cols$g ncols _stobj-name_)))))


     (defxdoc _stobj-name_
       :parents _parents_
       :short (or _short_
                  (str::cat "Abstract stobj that implements a two dimensional array
                             of "
                            (if (symbolp '_elt-typep_)
                                (str::cat "@(see " (xdoc::full-escape-symbol '_elt-typep_) ")s.")
                              (str::cat "elements satisfying <tt>"
                                        (str::rchars-to-string
                                         (xdoc::simple-html-encode-str '_elt-type-str_
                                                                       0 (length '_elt-type-str_) nil))
                                        "</tt>."))))
       :long (or _long_
                 (str::cat "<p>This is a two dimensional abstract stobj array,
                            introduced by @(see stobjs::def-2d-arr).</p>
                            @(def " (xdoc::full-escape-symbol '_stobj-name_) ")")))

     (defsection ext
       ;; Doing it this way, instead of putting it in the :long, lets you overwrite
       ;; the boilerplate :long above but still get the stobj definition.
       :extension _stobj-name_
       :long (str::cat "@(def " (xdoc::full-escape-symbol '_stobj-name_) ")"))

     ;; Hrmn, actually it's probably better NOT to generate docs for this, because
     ;; the user should never care about it.
     ;;
     ;; (defxdoc _stobj-name_p
     ;;   :parents (_stobj-name_)
     ;;   :short (str::cat "Recognizer for the @(see " (xdoc::full-escape-symbol '_stobj-name_) ") array.")
     ;;   :long (str::cat "<p>In guard obligations you will typically get to
     ;;                    assume this for free as a result of your
     ;;                    @('(declare (xargs :stobjs ...))') form.</p>
     ;;
     ;;                    <p>The logical definition is somewhat involved.  An
     ;;                    ordinary list of well-formed elements with no size
     ;;                    bound is recognized by:</p>
     ;;
     ;;                    @(def " (xdoc::full-escape-symbol '_prefix_e-datap) ")
     ;;
     ;;                    <p>We then recognize a list of well-formed rows of the
     ;;                    right length via:</p>
     ;;
     ;;                    @(def " (xdoc::full-escape-symbol '_prefix_l-arr2-data-wfp) ")
     ;;
     ;;                    <p>And the top-level recognizer wraps this up to ensure
     ;;                    that all of the rows have the same length as the first
     ;;                    row:</p>
     ;;
     ;;                    @(def " (xdoc::full-escape-symbol '_prefix_l-arr2-wfp) ")"))


     (defxdoc _prefix_-nrows
       :parents (_stobj-name_)
       :short (str::cat "Get the number of rows in the @(see "
                        (xdoc::full-escape-symbol '_stobj-name_) ") array.")
       :long (str::cat "<p>Logical definition:</p>
                        @(def " (xdoc::full-escape-symbol '_prefix_l-nrows) ")"))

     (defxdoc _prefix_-ncols
       :parents (_stobj-name_)
       :short (str::cat "Get the number of columns in the @(see "
                        (xdoc::full-escape-symbol '_stobj-name_) ") array.")
       :long (str::cat "<p>Logical definition:</p>
                       @(def " (xdoc::full-escape-symbol '_prefix_l-ncols) ")"))

     (defxdoc _prefix_-get2
       :parents (_stobj-name_)
       :short (str::cat "Get the element at @('arr[row][col]') from the @(see "
                        (xdoc::full-escape-symbol '_stobj-name_) ") array.")
       :long (str::cat "<p>Logical definition:</p>
                        @(def " (xdoc::full-escape-symbol '_prefix_l-get2) ")"))

     (defxdoc _prefix_-set2
       :parents (_stobj-name_)
       :short (str::cat "Set the element at @('arr[row][col]') in the @(see "
                        (xdoc::full-escape-symbol '_stobj-name_) ") array to
                        some new value.")
       :long (str::cat "<p>Logical definition:</p>
                       @(def " (xdoc::full-escape-symbol '_prefix_l-set2) ")"))

     (defxdoc _prefix_-resize-rows
       :parents (_stobj-name_)
       :short (str::cat "Change the number of rows in the @(see "
                        (xdoc::full-escape-symbol '_stobj-name_) "), preserving data.")
       :long (str::cat "<p>Logical definition:</p>
                       @(def " (xdoc::full-escape-symbol '_prefix_l-resize-rows) ")"))

     (defxdoc _prefix_-resize-cols
       :parents (_stobj-name_)
       :short (str::cat "Change the number of columns in the @(see "
                        (xdoc::full-escape-symbol '_stobj-name_) "), deleting data.")
       :long (str::cat "<p>Logical definition:</p>
                       @(def " (xdoc::full-escape-symbol '_prefix_l-resize-cols) ")"))

     (xdoc::order-subtopics _stobj-name_
                            (_prefix_-get2
                             _prefix_-set2
                             _prefix_-nrows
                             _prefix_-ncols
                             _prefix_-resize-rows
                             _prefix_-resize-cols))

     ))


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

(defmacro def-2d-arr (stobj-name
                      &key
                      prefix
                      (type-decl 't)
                      (pred       'true-predicate)
                      default-val
                      (fix 'id-macro) ;; function/lambda -- must be idempotent when elt-typep
                      (elt-guard 'true-predicate elt-guard-present-p)
                      (elt-okp   't)
                      (xvar      'acl2::x)
                      (parents   'nil parents-p)
                      short
                      long)
  `(make-event
    (b* ((base-pkg (pkg-witness (current-package state)))
         (parents (if ,parents-p
                      ',parents
                    (or (xdoc::get-default-parents (w state))
                        '(acl2::undocumented))))
         ((mv elt-type-str state) (xdoc::fmt-to-str-orig ',pred base-pkg state))
         (elt-guard (if ,elt-guard-present-p
                        ',elt-guard
                      '(,pred ,xvar)))
         (- (cw "elt-guard is ~x0~%" elt-guard))
         (symsubst-alist (list* (cons '_elt-type-str_ elt-type-str)
                                (cons '_elt-guard_    elt-guard)
                                (cons '_parents_      parents)
                                '((_elt-type_ . ,type-decl)
                                  (_elt-typep_ . ,pred)
                                  (_default-elt_ . ,default-val)
                                  (_elt-fix_ . ,fix)
                                  (_elt-okp_ . ,elt-okp)
                                  (_xvar_    . ,xvar)
                                  (_short_ . ,short)
                                  (_long_ . ,long))))
         (strsubst-alist '(("_STOBJ-NAME_" . ,(symbol-name stobj-name))
                           ("_PREFIX_" . ,(if prefix
                                              (symbol-name prefix)
                                            (symbol-name stobj-name)))))
         (events (sublis symsubst-alist
                         (sublis-symbol-substrs strsubst-alist
                                                (def2darr-events)
                                                ',stobj-name))))
      (value events))))


