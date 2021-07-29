; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>
;      (this file) Sol Swords <sswords@centtech.com>

(in-package "VL")
(include-book "expr-tools")
(include-book "../util/warnings")
(include-book "coretypes")
(include-book "../util/sum-nats")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "../util/default-hints"))
(local (std::add-default-post-define-hook :fix))

(defxdoc datatype-tools
  :parents (mlib)
  :short "Functions for working with datatypes.")

(local (xdoc::set-default-parents datatype-tools))


(define vl-hidexpr-name1 ((x vl-hidexpr-p))
  :returns (name vl-hidname-p
                 :hints ((and stable-under-simplificationp
                              '(:in-theory (enable vl-hidname-p)))))
  (vl-hidexpr-case x
    :end x.name
    :dot (vl-hidindex->name x.first)))
    


(defines vl-datatype-resolved-p
  (define vl-datatype-resolved-p ((x vl-datatype-p))
    :measure (vl-datatype-count x)
    (vl-datatype-case x
      :vl-coretype t
      :vl-struct (vl-structmemberlist-resolved-p x.members)
      :vl-union  (vl-structmemberlist-resolved-p x.members)
      :vl-enum   (vl-datatype-resolved-p x.basetype)
      :vl-usertype (and x.res
                        (vl-datatype-resolved-p x.res))))

  (define vl-structmemberlist-resolved-p ((x vl-structmemberlist-p))
    :measure (vl-structmemberlist-count x)
    (if (atom x)
        t
      (and (vl-datatype-resolved-p (vl-structmember->type (car x)))
           (vl-structmemberlist-resolved-p (cdr x)))))
  ///
  (deffixequiv-mutual vl-datatype-resolved-p)

  (defthm vl-datatype-resolved-p-of-make-coretype
    (vl-datatype-resolved-p (vl-coretype name signedp pdims udims)))

  (defthm vl-datatype-resolved-p-of-make-struct
    (equal (vl-datatype-resolved-p (make-vl-struct :packedp packedp
                                                   :signedp signedp
                                                   :members members
                                                   :pdims pdims
                                                   :udims udims))
           (vl-structmemberlist-resolved-p members))
    :hints (("goal" :expand ((vl-datatype-resolved-p
                              (make-vl-struct :packedp packedp
                                              :signedp signedp
                                              :members members
                                              :pdims pdims
                                              :udims udims))))))

  (defthm vl-datatype-resolved-p-of-make-union
    (equal (vl-datatype-resolved-p (make-vl-union :packedp packedp
                                                  :signedp signedp
                                                  :taggedp taggedp
                                                  :members members
                                                  :pdims pdims
                                                  :udims udims))
           (vl-structmemberlist-resolved-p members))
    :hints (("Goal" :expand ((vl-datatype-resolved-p
                              (make-vl-union :packedp packedp
                                             :signedp signedp
                                             :taggedp taggedp
                                             :members members
                                             :pdims pdims
                                             :udims udims))))))

  (defthm vl-datatype-resolved-p-of-make-enum
    (equal (vl-datatype-resolved-p (make-vl-enum :basetype basetype
                                                 :items items
                                                 :values values
                                                 :pdims pdims
                                                 :udims udims))
           (vl-datatype-resolved-p basetype))
    :hints (("goal" :expand (vl-datatype-resolved-p (make-vl-enum :basetype basetype
                                                                  :items items
                                                                  :values values
                                                                  :pdims pdims
                                                                  :udims udims)))))

  (defthm vl-datatype-resolved-p-of-make-usertype
    (equal (vl-datatype-resolved-p (make-vl-usertype :name name
                                                     :res res
                                                     :pdims pdims
                                                     :udims udims
                                                     :virtual-intfc virtual-intfc
                                                     :intfc-params intfc-params))
           (and res (vl-datatype-resolved-p res)))
    :hints (("Goal" :expand (vl-datatype-resolved-p (make-vl-usertype :name name
                                                                      :res res
                                                                      :pdims pdims
                                                                      :udims udims
                                                                      :virtual-intfc virtual-intfc
                                                                      :intfc-params intfc-params)))))

  (defthm vl-structmemberlist-resolved-p-of-struct-members
    (implies (and (vl-datatype-case x :vl-struct)
                  (vl-datatype-resolved-p x))
             (vl-structmemberlist-resolved-p (vl-struct->members x))))

  (defthm vl-structmemberlist-resolved-p-of-union-members
    (implies (and (vl-datatype-case x :vl-union)
                  (vl-datatype-resolved-p x))
             (vl-structmemberlist-resolved-p (vl-union->members x))))

  (defthm vl-datatype-resolved-p-of-enum-basetype
    (implies (and (vl-datatype-case x :vl-enum)
                  (vl-datatype-resolved-p x))
             (vl-datatype-resolved-p (vl-enum->basetype x))))

  (defthm vl-datatype-resolved-p-of-usertype-basetype
    (implies (and (vl-datatype-case x :vl-usertype)
                  (vl-datatype-resolved-p x))
             (and (vl-datatype-resolved-p (vl-usertype->res x))
                  (vl-usertype->res x))))

  (defthm vl-structmemberlist-resolved-p-of-cons
    (equal (vl-structmemberlist-resolved-p (cons a b))
           (and (vl-datatype-resolved-p (vl-structmember->type a))
                (vl-structmemberlist-resolved-p b))))

  (defthm vl-datatype-resolved-p-of-car-structmember-type
    (implies (vl-structmemberlist-resolved-p x)
             (vl-datatype-resolved-p (vl-structmember->type (car x)))))

  (defthm vl-structmemberlist-resolved-p-of-cdr
    (implies (vl-structmemberlist-resolved-p x)
             (vl-structmemberlist-resolved-p (cdr x))))

  (defthm vl-datatype-resolved-p-of-update-dims
    (implies (vl-datatype-resolved-p x)
             (vl-datatype-resolved-p (vl-datatype-update-dims pdims udims x)))
    :hints(("Goal" :in-theory (enable vl-datatype-update-dims)))))


(fty::deflist maybe-nat-list :elt-type maybe-natp
  ///
  (defthm nat-listp-when-maybe-nat-list-and-no-nils
    (implies (and (maybe-nat-list-p x)
                  (not (member nil x)))
             (nat-listp x))
    :hints(("Goal" :in-theory (enable maybe-nat-list-p member nat-listp)))))

(define vl-dimension-size ((x vl-dimension-p))
  :returns (mv (unresolved-flg)
               (size maybe-posp :rule-classes :type-prescription))
  (vl-dimension-case x
    :unsized  (mv nil nil) ;; Dynamic array, not unresolved, but has no sensible size
    :star     (mv nil nil) ;; Sparse associative array, similar
    :datatype (mv nil nil) ;; Sparse associative array, similar
    :queue
    (cond ((not x.maxsize)
           ;; An unbounded queue -- resolved but sizeless, like an unsized dimension
           (mv nil nil))
          ((vl-expr-resolved-p x.maxsize)
           ;; Possibly we could regard bounded queues as having a particular
           ;; size, but I'm not sure what size makes sense.  For now I'm going
           ;; to say they have no size.
           (mv nil nil))
          (t
           ;; The queue has a max size that isn't resolved.  Should we treat
           ;; these as having unresolved size?  What does unresolved-flg even
           ;; mean?  For now I'm going to still regard these as resolved, but
           ;; simply size-less.
           (mv t nil)))
    :range
    (if (vl-range-resolved-p x.range)
        (mv nil (vl-range-size x.range))
      (mv t nil))))

(define vl-maybe-dimension-size ((x vl-maybe-dimension-p))
  :returns (mv (unresolved-flg)
               (size maybe-posp :rule-classes :type-prescription))
  (if x
      (vl-dimension-size x)
    (mv nil nil)))

(define vl-dimensionlist-resolved-p ((x vl-dimensionlist-p))
  :short "Returns true if all sized dimensions are resolved."
  (b* (((when (atom x)) t)
       ((mv unresolved ?size) (vl-dimension-size (car x))))
    (and (not unresolved)
         (vl-dimensionlist-resolved-p (cdr x))))
  ///

  (defthm vl-dimensionlist-resolved-p-when-atom
    (implies (atom x)
             (vl-dimensionlist-resolved-p x)))

  (defthm vl-dimensionlist-resolved-p-of-cons
    (equal (vl-dimensionlist-resolved-p (cons a x))
           (and (b* (((mv unresolved ?size) (vl-dimension-size a)))
                  (not unresolved))
                (vl-dimensionlist-resolved-p x))))

  (defthm vl-dimensionlist-resolved-p-of-cdr
    (implies (vl-dimensionlist-resolved-p x)
             (vl-dimensionlist-resolved-p (cdr x))))

  (defthm vl-dimensionlist-resolved-p-of-append
    (equal (vl-dimensionlist-resolved-p (append x y))
           (and (vl-dimensionlist-resolved-p x)
                (vl-dimensionlist-resolved-p y)))))

(define vl-dimensionlist-total-size ((x vl-dimensionlist-p))
  :short "Given a dimensionlist like [5:0][3:1][0:8], multiplies the
dimensions together to get the total number of bits, or returns nil if there
are unsized dimensions (e.g., associative dimensions, queue dimensions, or
dynamic array dimensions)."
  :guard (vl-dimensionlist-resolved-p x)
  :verify-guards nil
  :returns (size maybe-posp :rule-classes :type-prescription)
  (b* (((when (atom x)) 1)
       (rest-size (vl-dimensionlist-total-size (cdr x)))
       ((unless rest-size) nil)
       ((mv first-unresolved first-size) (vl-dimension-size (car x)))
       ((when (or first-unresolved
                  (not first-size)))
        nil))
    (* first-size rest-size))
  ///
  (verify-guards vl-dimensionlist-total-size
    :hints (("goal" :in-theory (enable vl-dimensionlist-resolved-p))))

  (defthm vl-dimensionlist-total-size-of-cdr
    (implies (vl-dimensionlist-total-size x)
             (vl-dimensionlist-total-size (cdr x)))
    :rule-classes (:rewrite :type-prescription))

  (defthm vl-dimensionlist-total-size-of-append
    (equal (vl-dimensionlist-total-size (append x y))
           (and (vl-dimensionlist-total-size x)
                (vl-dimensionlist-total-size y)
                (* (vl-dimensionlist-total-size x)
                   (vl-dimensionlist-total-size y))))))

(defines vl-datatype-size
  :prepwork ((local (in-theory (disable all-equalp
                                        default-*-1
                                        rationalp-implies-acl2-numberp
                                        double-containment)))
             (std::set-returnspec-mrec-default-hints
              ((acl2::just-expand-mrec-default-hint 'std::fnname id nil world))))
  (define vl-datatype-size ((x vl-datatype-p "The datatype to size"))
    :short "Computes the number of bits in the datatype."
    :long "<p>This works for unpacked datatypes as well as packed ones; you
should check separately that the datatype is packed if that is what you want.
Returns nil without error if given a datatype that has no fixed bit size,
e.g. if it contains a real number or has unsized dimensions.  We produce an
error message if a usertype is not found, if the recursion limit runs out, or
if unresolved dimensions are present.</p>"

    :measure (vl-datatype-count x)
    :guard (vl-datatype-resolved-p x)
    :returns (mv (err (iff (vl-msg-p err) err))
                 (size maybe-natp :rule-classes :type-prescription))
    :verify-guards nil
    (b* ((x (vl-datatype-fix x))
         (udims (vl-datatype->udims x))
         (pdims (vl-datatype->pdims x))
         ((unless (vl-dimensionlist-resolved-p udims))
          (mv (vmsg "Unresolved unpacked dimensions: ~a0" x)
              nil))
         ((unless (vl-dimensionlist-resolved-p pdims))
          (mv (vmsg "Unresolved packed dimensions: ~a0" x)
              nil))
         (udim-size (vl-dimensionlist-total-size udims))
         (pdim-size (vl-dimensionlist-total-size pdims))
         (dim-size (and udim-size pdim-size (* udim-size pdim-size))))

      (vl-datatype-case x
        (:vl-coretype
         (b* (((vl-coredatatype-info typinfo) (vl-coretypename->info x.name)))
           (mv nil (and typinfo.size dim-size
                        (* typinfo.size dim-size)))))

        (:vl-struct
         (b* (((mv err widths) (vl-structmemberlist-sizes x.members))
              ((when err) (mv err nil))
              ((when (member nil widths)) (mv nil nil)))
           (mv nil (and dim-size (* (sum-nats widths) dim-size)))))

        (:vl-union
         (b* (((mv err widths) (vl-structmemberlist-sizes x.members))
              ((when err) (mv err nil))
              ((when (member nil widths)) (mv nil nil)))
           (mv nil (and dim-size (* (max-nats widths) dim-size)))))

        (:vl-enum
         (b* (((mv err sub-size)
               (vl-datatype-size x.basetype))
              ((when (or err (not sub-size)))
               (mv err nil)))
           (mv nil (and dim-size (* sub-size dim-size)))))

        (:vl-usertype
         (b* (((unless (mbt (and x.res t)))
               (mv (vmsg "Usertype unresolved: ~a0" x) nil))
              ((mv err sub-size)
               (vl-datatype-size x.res))
              ((when (or err (not sub-size)))
               (mv err nil)))
           (mv nil (and dim-size (* sub-size dim-size))))))))

  (define vl-structmemberlist-sizes ((x vl-structmemberlist-p))
    :returns (mv (err (iff (vl-msg-p err) err))
                 (sizes maybe-nat-list-p))
    :guard (vl-structmemberlist-resolved-p x)
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x)) (mv nil nil))
         ((mv err1 size1) (vl-datatype-size (vl-structmember->type (car x))))
         ((mv err2 size2) (vl-structmemberlist-sizes (cdr x))))
      (mv (or err1 err2) (cons size1 size2)))
    ///
    (defret len-of-vl-structmemberlist-sizes
      (equal (len sizes)
             (len x))
      :hints (("goal" :induct (len x)
               :expand ((vl-structmemberlist-sizes x)))))
    (defret true-listp-of-vl-structmemberlist-sizes
      (true-listp sizes)
      :hints (("goal" :induct (len x)
               :expand ((vl-structmemberlist-sizes x))))
      :rule-classes :type-prescription))
  ///

  (defthm-vl-datatype-size-flag
    (defthm vl-datatype-size-not-err-when-size
      (b* (((mv err size) (vl-datatype-size x)))
        (implies size
                 (not err)))
      :hints ('(:expand ((vl-datatype-size x))))
      :flag vl-datatype-size)
    (defthm vl-structmemberlist-sizes-not-err-when-sizes
      (b* (((mv err sizes) (vl-structmemberlist-sizes x)))
        (implies (not (member nil sizes))
                 (not err)))
      :hints ('(:expand ((vl-structmemberlist-sizes x))))
      :flag vl-structmemberlist-sizes))


  (verify-guards vl-datatype-size)
  (deffixequiv-mutual vl-datatype-size))


(defines vl-datatype-has-usertypes
  (define vl-datatype-has-usertypes ((x vl-datatype-p))
    :measure (Vl-datatype-count x)
    (vl-datatype-case x
      :vl-coretype nil
      :vl-struct (vl-structmemberlist-has-usertypes x.members)
      :vl-union (vl-structmemberlist-has-usertypes x.members)
      :vl-enum (vl-datatype-has-usertypes x.basetype)
      :vl-usertype t))
  (define vl-structmemberlist-has-usertypes ((x vl-structmemberlist-p))
    :measure (vl-structmemberlist-count x)
    (if (atom x)
        nil
      (or (vl-datatype-has-usertypes (vl-structmember->type (car x)))
          (vl-structmemberlist-has-usertypes (cdr x))))))


(define vl-maybe-usertype-resolve ((x vl-datatype-p))
  :guard (vl-datatype-resolved-p x)
  :returns (new-x vl-datatype-p)
  :measure (vl-datatype-count x)
  (b* ((x (vl-datatype-fix x))
       ((when (or (consp (vl-datatype->pdims x))
                  (consp (vl-datatype->udims x))))
        x))
    (vl-datatype-case x
      :vl-usertype (if x.res
                       (vl-maybe-usertype-resolve x.res)
                     x)
      :otherwise x))
  ///
  (defret vl-datatype-count-of-vl-maybe-usertype-resolve
    (<= (vl-datatype-count new-x)
        (vl-datatype-count x))
    :rule-classes :linear)

  (defret vl-datatype-resolved-p-of-vl-maybe-usertype-resolve
    (implies (vl-datatype-resolved-p x)
             (vl-datatype-resolved-p new-x)))

  (local (defret vl-maybe-usertype-resolve-nonnil
           new-x
           :rule-classes :type-prescription))

  (defret not-usertype-of-vl-maybe-usertype-resolve
    (implies (and (not (consp (vl-datatype->pdims new-x)))
                  (not (consp (vl-datatype->udims new-x)))
                  (vl-datatype-resolved-p x))
             (not (equal (vl-datatype-kind new-x)  :vl-usertype)))
    :rule-classes
    ((:forward-chaining :trigger-terms
      ((vl-datatype-kind (vl-maybe-usertype-resolve x)))))))




(define vl-datatype-packedp ((x vl-datatype-p))
  :guard (vl-datatype-resolved-p x)
  :short "Decide whether the datatype is packed or not."
  :long "<p>A shallow check; e.g. we don't check for invalid things such as a
packed struct with a member that's an unpacked array.</p>

<p>Note that the question of whether something is packed is subtly different
from the question of whether you can select from it: namely, simple bit types
such as @('logic') are packed but not selectable.</p>"
  :returns (packedp)
  (b* ((x (vl-maybe-usertype-resolve x))
       ((when (consp (vl-datatype->udims x))) nil)
       ((when (consp (vl-datatype->pdims x))) t))
    (vl-datatype-case x
      :vl-coretype
      (b* (((vl-coredatatype-info xinfo) (vl-coretypename->info x.name)))
        (and xinfo.size t))
      :vl-struct x.packedp
      :vl-union x.packedp
      :vl-enum t
      :vl-usertype (impossible))))

