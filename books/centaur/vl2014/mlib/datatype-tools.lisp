; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "scopestack")
(include-book "range-tools")
(include-book "coretypes")
(include-book "../util/sum-nats")
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))
(local (in-theory (disable append)))

(defxdoc datatype-tools
  :parents (mlib)
  :short "Functions for working with datatypes.")

(local (xdoc::set-default-parents datatype-tools))

(define vl-usertype-resolve ((x vl-datatype-p)
                             (ss vl-scopestack-p)
                             (rec-limit natp))
  :guard (eq (vl-datatype-kind x) :vl-usertype)
  :short "Resolves a datatype of usertype kind to a concrete
datatype, i.e. anything but a user typename."
  :long "<p>The input is guarded to be a usertype.  If it is defined as another
usertype (possibly with packed/unpacked dimensions), then we recur until it is
defined as something other than a usertype.  However, the final type may still
have usertypes within it, i.e. as struct/union member types.</p>

<p>Also returns the scopestack representing the scope in which the
final type declaration was found.</p>

<p>This function is strict with respect to packed vs. unpacked dimensions;
i.e., if a usertype is defined as having unpacked dimensions, it will warn if
any packed dimensions are applied to that type.  Arguably this check should be
done elsewhere, in which case this function could ignore the distinction
between packed and unpacked dimensions.  However, it is important to preserve
the order of dimensions, and it's not clear how to handle cases that mix the
two: packed dimensions are always treated as \"inner\" or \"most rapidly
varying\" dimensions.  So if we have (illegal) nested typedefs that place
unpacked dimensions inside of packed dimensions, we have no way to express that
as a single, usertype-free datatype, unless we change some packed dimensions
into unpacked ones or vice versa:</p>

@({
 typedef logic t1 [5:1];  // unpacked dimension
 typedef t1 [3:0] t2;     // packed dimension applied to unpacked datatype

 typedef logic [3:0] t3 [5:1];  // not the same as t2

 typedef logic [5:1] [3:0] t4;  // same dimensions as t2, but all dimensions packed
 typedef logic t5 [5:1] [3:0];  // same dimensions as t2, but all dimensions unpacked
 })

<p>We don't have this problem for the (also illegal) case where packed
dimensions are applied to an unpacked structure or union, so we don't warn in
this case; this should be checked separately.</p>"

  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (type vl-datatype-p)
               (scope vl-scopestack-p))
  :measure (nfix rec-limit)
  :verify-guards nil
  (b* ((ss (vl-scopestack-fix ss))
       (x (vl-datatype-fix x))
       ((vl-usertype x))
       ((when (zp rec-limit))
        (mv (make-vl-warning :type :vl-resolve-usertypes-fail
                             :msg "Rec-limit ran out: recursively defined ~
                                       datatype? ~a0"
                             :args (list x.kind))
            x ss))
       ((unless (and (vl-atom-p x.kind)
                     (member (tag (vl-atom->guts x.kind)) '(:vl-id :vl-typename))))
        (mv (make-vl-warning :type :vl-resolve-usertypes-fail
                             :msg "We don't yet support usertypes that are ~
                                   not simple identifiers: ~a0"
                             :args (list x.kind))
            x ss))
       (guts (vl-atom->guts x.kind))
       (name (if (eq (tag guts) :vl-id)
                 (vl-id->name guts)
               (vl-typename->name guts)))
       ((mv item new-ss)
        (vl-scopestack-find-item/ss name ss))
       ((unless item)
        (mv (make-vl-warning :type :vl-resolve-usertypes-fail
                             :msg "No typedef found for ~a0"
                             :args (list x.kind))
            x ss))
       ((unless (eq (tag item) :vl-typedef))
        (mv (make-vl-warning :type :vl-resolve-usertypes-fail
                             :msg "Didn't find a typedef ~a0, instead ~
                                       found ~a1"
                             :args (list x.kind item))
            x ss))
       ((vl-typedef item))
       ((mv warning subtype final-ss)
        (if (eq (vl-datatype-kind item.type) :vl-usertype)
            (vl-usertype-resolve item.type new-ss (1- rec-limit))
          (mv nil item.type new-ss)))
       ((when warning)
        (mv warning x ss))
       (sub-udims (vl-datatype->udims subtype))
       ((when (and (consp x.pdims) (consp (vl-datatype->udims item.type))))
        ;; Bad case: we have unpacked dimensions from the inner call but
        ;; we're trying to add packed ones.  Warn and return x.
        (mv (make-vl-warning :type :vl-usertype-packed-dims
                             :msg "Usertype ~a0 was declared with packed ~
                                       dimensions, but its definition ~a1 already ~
                                       has unpacked dimensions."
                             :args (list x item.type))
            x ss))
       (subtype (mbe :logic (vl-datatype-update-dims
                             (append-without-guard x.pdims (vl-datatype->pdims subtype))
                             (append-without-guard x.udims sub-udims)
                             subtype)
                     :exec
                     (if (or x.udims x.pdims)
                         (vl-datatype-update-dims
                          (append-without-guard x.pdims (vl-datatype->pdims subtype))
                          (append-without-guard x.udims sub-udims)
                          subtype)
                       subtype))))
    (mv nil subtype final-ss))
  ///

  (verify-guards vl-usertype-resolve))



(defines vl-datatype-usertype-elim
  :verify-guards nil
  (define vl-datatype-usertype-elim ((x vl-datatype-p)
                                         (ss vl-scopestack-p)
                                         (reclimit natp))
    :measure (two-nats-measure reclimit (vl-datatype-count x))
    :returns (mv (warning (iff (vl-warning-p warning) warning))
                 (type vl-datatype-p))
    :short "Resolves all usertypes within a datatype, recursively."
    :long "<p>A recursion limit is needed in case a usertype is defined in
terms of itself.</p>

<p>Always returns a datatype; however, when a warning is present, it may still
contain usertypes.</p>

<p>This function (actually its subroutine, @(see vl-usertype-resolve)) is
somewhat strict with respect to packed vs. unpacked dimensions; see @(see
vl-usertype-resolve) for a more extensive discussion.</p>

<p>An example to work through: suppose we want to resolve the usertype memchunk
into a usertype-free datatype --</p>

@({
  typedef logic [3:0] mynibble;
  typedef mynibble [7:0] my32;
  typedef my32 [0:3] membank [63:0];
  // error: since membank now has unpacked dims, we can't give it more packed dims:
  // typedef membank [3:0] memchunk;
  // this works:
  typedef membank memchunk [3:0];
 })"
    (b* ((x (vl-datatype-fix x)))
      (vl-datatype-case x
        :vl-coretype (mv nil x)
        :vl-enum (mv nil x) ;; bozo
        :vl-usertype
        (b* (((mv warning newx newss) (vl-usertype-resolve x ss 100))
             ((when warning) (mv warning newx))
             ((when (zp reclimit))
              (mv (make-vl-warning :type :vl-datatype-usertype-elim-fail
                                   :msg "Recursion limit ran out: ~a0"
                                   :args (list x.kind))
                  newx)))
          (vl-datatype-usertype-elim newx newss (1- reclimit)))
        :vl-struct
        (b* (((mv warning members) (vl-structmembers-usertype-elim x.members ss reclimit))
             (newx (change-vl-struct x :members members)))
          (mv warning newx))
        :vl-union
        (b* (((mv warning members) (vl-structmembers-usertype-elim x.members ss reclimit))
             (newx (change-vl-union x :members members)))
          (mv warning newx)))))
  (define vl-structmembers-usertype-elim ((x vl-structmemberlist-p)
                                              (ss vl-scopestack-p)
                                              (reclimit natp))
    :measure (two-nats-measure reclimit (vl-structmemberlist-count x))
    :returns (mv (warning (iff (vl-warning-p warning) warning))
                 (newx vl-structmemberlist-p))
    (b* (((when (atom x)) (mv nil nil))
         ((mv warning type1) (vl-datatype-usertype-elim
                              (vl-structmember->type (car x)) ss reclimit))
         (first (change-vl-structmember (car x) :type type1))
         ((when warning) (mv warning (cons first (vl-structmemberlist-fix (cdr x)))))
         ((mv warning membs2) (vl-structmembers-usertype-elim (cdr x) ss reclimit)))
      (mv warning (cons first membs2))))
  ///
  (verify-guards vl-datatype-usertype-elim)
  (deffixequiv-mutual vl-datatype-usertype-elim))


(define vl-datatype->structmembers ((x vl-datatype-p))
  :short "Finds the struct members of x when it is a struct or union."
  :returns (mv ok (members vl-structmemberlist-p))
  (vl-datatype-case x
    :vl-struct (mv t x.members)
    :vl-union  (mv t x.members)
    :otherwise (mv nil nil)))

(define vl-find-structmember ((name stringp) (membs vl-structmemberlist-p))
  :returns (memb (iff (vl-structmember-p memb) memb))
  (if (atom membs)
      nil
    (if (equal (string-fix name) (vl-structmember->name (car membs)))
        (vl-structmember-fix (car membs))
      (vl-find-structmember name (cdr membs)))))


(define vl-packeddimensionlist-total-size ((x vl-packeddimensionlist-p))
  :short "Given a packeddimensionlist like [5:0][3:1][0:8], multiplies the
dimensions together to get the total number of bits, or returns nil on
failure."
  :returns (size maybe-posp :rule-classes :type-prescription)
  (b* (((when (atom x)) 1)
       (rest (vl-packeddimensionlist-total-size (cdr x)))
       ((unless rest) nil)
       (first (vl-packeddimension-fix (car x)))
       ((when (eq first :vl-unsized-dimension)) nil)
       ((unless (vl-range-resolved-p first)) nil))
    (* (vl-range-size first) rest)))


(define vl-datatype-range
  :short "Get the range, if any, for a data type."
  :long "<p>The datatype should be fully resolved, as in the output from @(see
vl-datatype-usertype-elim).</p>

<p>What exactly do we mean by the range of a datatype?  Most data types can
have multiple array dimensions.  What we mean is the range of indices that are
valid to apply directly to the data structure: that is, the range of the
\"first\" array dimension.  This means: the leftmost unpacked dimension if
there are unpacked dimensions; otherwise the leftmost packed dimension,
otherwise nil.  When types are composed, e.g. by declaring a type to be another
type with some additional dimensions, the additional dimensions go to the left.
Examples:</p>

@({
    typedef logic [3:0] nibble;
    typedef nibble [7:0] quadword [1:0];
    typedef quadword cacheline [15:0];
})

<p>These are equivalent to:</p>
@({
 typedef logic [3:0] nibble;
 typedef logic [7:0] [3:0] quadword [1:0];
 typedef logic [7:0] [3:0] cacheline [15:0] [1:0];
 })

<p>A tricky part here is that a variable declaration's datatype doesn't
necessarily include all of the unpacked array dimensions.  In the declaration
of my_kbyte, the type of my_kbyte is dword but it has additional dimensions
stored in the variable declaration itself.  So we take as an extra argument the
unpacked dimensions of the datatype.  If there are any unpacked dimensions,
then the first unpacked dimension is transformed into the range; otherwise,
it's the first packed dimension (or the declared range of a net type).</p>"
  ((x vl-datatype-p))
  :returns
  (mv (warning (iff (vl-warning-p warning) warning))
      (range  vl-maybe-range-p
              "On success: the range of this datatype."))
  (b* (((fun (fail msg args))
        (mv (make-vl-warning :type :vl-datatype-range-fail
                             :msg msg
                             :args args)
            nil))
       ((fun (success range)) (mv nil range))
       (x (vl-datatype-fix x))
       (udims (vl-datatype->udims x))
       ((when (consp udims))
        (b* ((dim (vl-packeddimension-fix (car udims)))
             ((when (eq dim :vl-unsized-dimension))
              (fail "Most significant dimension is unsized: ~a0" (list x))))
          (success dim)))
       (pdims (vl-datatype->pdims x))
       ((when (consp pdims))
        (b* (((when (eq (car pdims) :vl-unsized-dimension))
              (fail "Most significant dimension is unsized: ~a0" (list x))))
          (success (car pdims)))))
    ;; No array dimensions, and not a nettype.  Do we succeed with NIL or fail?
    ;; What we want depends on whether we only call this due to some indexing
    ;; operation, or whether we call this in an exploratory fashion.  At the
    ;; moment, we return NIL and the caller should produce an error if this is
    ;; bad.
    (success nil)))




(define vl-datatype-range-conservative
  :short "Get the range, if any, for a data type."
  :long "<p>The datatype should be fully resolved, as in the output from @(see
vl-datatype-usertype-elim).</p>

<p>This is like @(see vl-datatype-range), but it only works on
single-dimensional vectors of basic 1-bit types.  Why?  A lot of existing code
is built around an assumption that the range of a variable determines its
width.  In that code, if we use vl-datatype-range, then we'll be silently doing
the wrong thing in a lot of cases.</p>."
  ((x vl-datatype-p))
  :returns
  (mv (warning (iff (vl-warning-p warning) warning))
      (range  vl-maybe-range-p
              "On success: the range of this datatype."))
  (b* (((fun (fail msg args))
        (mv (make-vl-warning :type :vl-datatype-range-fail
                             :msg msg
                             :args args)
            nil))
       ((fun (success range)) (mv nil range))
       (x (vl-datatype-fix x))
       (udims (vl-datatype->udims x))
       ((when (consp udims))
        (fail "Unpacked dims present." nil))
       ((when (and (eq (vl-datatype-kind x) :vl-coretype)
                   (member (vl-coretype->name x)
                           '(:vl-logic :vl-reg :vl-bit))))
        (b* ((dims (vl-coretype->pdims x))
             ((when (atom dims)) (success nil))
             ((when (and (atom (cdr dims))
                         (not (eq (car dims) :vl-unsized-dimension))))
              (success (car dims))))
          (fail "Multiple packed dims present" nil))))
    (fail "Complex type." nil)))



(defines vl-packed-datatype-size
  :verify-guards nil
  :prepwork ((local (defthm posp-sum-nats-of-pos-listp
                      (implies (and (pos-listp x) (consp x))
                               (posp (sum-nats x)))
                      :hints(("Goal" :in-theory (enable sum-nats)))
                      :rule-classes (:rewrite :type-prescription)))
             (local (defthm posp-max-nats-of-pos-listp
                      (implies (and (pos-listp x) (consp x))
                               (posp (max-nats x)))
                      :hints(("Goal" :in-theory (enable max-nats)))
                      :rule-classes (:rewrite :type-prescription)))
             (local (defthm posp-product
                      (implies (and (posp x) (posp y))
                               (posp (* x y))))))
  (define vl-packed-datatype-size
    :short "Get the size for any packed data type."
    :long "<p>The type should be fully resolved (i.e. no usertypes) and be
packed or we'll fail.</p>"
    ((x vl-datatype-p))
    :returns
    (mv (warning (iff (vl-warning-p warning) warning))
        (size    (implies (not warning) (posp size)) :rule-classes :type-prescription))
    :measure (vl-datatype-count x)
    (b* (((fun (fail reason args))
          (mv (make-vl-warning :type :vl-datatype-size-fail
                               :msg reason
                               :args args)
              nil))
         ((fun (success width)) (mv nil width))
         (x (vl-datatype-fix x))
         ((when (consp (vl-datatype->udims x)))
          (fail "Has unpacked dimensions: ~a0" (list x))))

      (vl-datatype-case x

        (:vl-coretype
         (b* ((totalsize (vl-packeddimensionlist-total-size x.pdims)))
           (if totalsize
               (case x.name
                 ;; See SystemVerilog-2012 Section 6.11, Integer Data Types.

                 ;; integer atom types -- these don't have any dimensions, they're just fixed sizes
                 (:vl-byte     (success (* 8 totalsize)))
                 (:vl-shortint (success (* 16 totalsize)))
                 (:vl-int      (success (* 32 totalsize)))
                 (:vl-longint  (success (* 64 totalsize)))
                 (:vl-integer  (success (* 32 totalsize)))
                 (:vl-time     (success (* 64 totalsize)))

                 ;; integer vector types -- these have arbitrary packed dimensions.
                 ((:vl-bit :vl-logic :vl-reg)
                  (success totalsize))

                 (otherwise
                  ;; Something like a real, shortreal, void, realtime, chandle, etc.
                  ;; We don't try to size these, but we still claim success: these just
                  ;; don't have ranges.
                  (fail "bad coretype ~a0" (list x))))
             (fail "Dimensions of vector type ~a0 not resolvd"
                   (list x)))))

        (:vl-struct
         (b* (((unless x.packedp) (fail "unpacked struct ~a0" (list x)))
              ;; bozo is there a correct thing to do for a struct with no members?
              ((unless (consp x.members)) (fail "empty struct: ~a0" (list x)))
              ((mv warning widths) (vl-packed-structmemberlist-sizes x.members))
              ((when warning) (mv warning nil))
              (packedsize (vl-packeddimensionlist-total-size x.pdims))
              ((unless packedsize)
               (fail "Dimensions of struct type ~a0 not resolvd"
                      (list x))))
           (success (* packedsize (sum-nats widths)))))

        (:vl-union
         (b* (((unless x.packedp) (fail "unpacked union ~a0" (list x)))
              ;; bozo is there a correct thing to do for a union with no members?
              ((unless (consp x.members)) (fail "empty union ~a0" (list x)))
              ((mv warning widths) (vl-packed-structmemberlist-sizes x.members))
              ((when warning) (mv warning nil))
              (packedsize (vl-packeddimensionlist-total-size x.pdims))
              ((unless packedsize)
               (fail "Dimensions of struct type ~a0 not resolvd"
                      (list x))))
           (success (* packedsize (max-nats widths)))))

        (:vl-enum ;; need to compute size from the base type?
         (fail "bozo: implement enum range" nil))

        (:vl-usertype
         (fail "unresolved usertype: ~a0" (list x.kind))))))

  (define vl-packed-structmemberlist-sizes ((x vl-structmemberlist-p))
    :returns (mv (warning (iff (vl-warning-p warning) warning))
                 (sizes   (and (pos-listp sizes)
                               (implies (not warning)
                                        (equal (consp sizes) (consp x))))))
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x)) (mv nil nil))
         ((vl-structmember first) (vl-structmember-fix (car x)))
         ((mv warning size) (vl-packed-datatype-size first.type))
         ((when warning) (mv warning nil))
         ((mv warning rest) (vl-packed-structmemberlist-sizes (cdr x)))
         ((when warning) (mv warning nil)))
      (mv nil (cons size rest))))
  ///
  (defthm-vl-packed-datatype-size-flag
    (defthm len-of-vl-packed-structmemberlist-sizes
      (b* (((mv warning sizes) (vl-packed-structmemberlist-sizes x)))
        (implies (not warning)
                 (equal (len sizes) (len x))))
      :flag vl-packed-structmemberlist-sizes)
    :skip-others t)

  (local (defthm nat-listp-when-pos-listp
           (implies (pos-listp x)
                    (nat-listp x))
           :hints(("Goal" :in-theory (enable nat-listp)))))

  (verify-guards vl-packed-datatype-size)

  (deffixequiv-mutual vl-packed-datatype-size))

(defines vl-datatype-size
  :verify-guards nil
  :prepwork ((local (defthm posp-sum-nats-of-pos-listp
                      (implies (and (pos-listp x) (consp x))
                               (posp (sum-nats x)))
                      :hints(("Goal" :in-theory (enable sum-nats)))
                      :rule-classes (:rewrite :type-prescription)))
             (local (defthm posp-max-nats-of-pos-listp
                      (implies (and (pos-listp x) (consp x))
                               (posp (max-nats x)))
                      :hints(("Goal" :in-theory (enable max-nats)))
                      :rule-classes (:rewrite :type-prescription)))
             (local (defthm posp-product
                      (implies (and (posp x) (posp y))
                               (posp (* x y))))))
  (define vl-datatype-size
    :short "Get the size for a data type, including unpacked dimensions."
    :long "<p>The type should be fully resolved (i.e. no usertypes) or we'll fail.</p>"
    ((x vl-datatype-p))
    :returns
    (mv (warning (iff (vl-warning-p warning) warning))
        (size    (implies (not warning) (posp size)) :rule-classes :type-prescription))
    :measure (vl-datatype-count x)
    (b* (((fun (fail reason args))
          (mv (make-vl-warning :type :vl-datatype-size-fail
                               :msg reason
                               :args args)
              nil))
         ((fun (success width)) (mv nil width))
         (x (vl-datatype-fix x)))

      (vl-datatype-case x

        (:vl-coretype
         (b* ((udim-size (vl-packeddimensionlist-total-size x.udims))
              (pdim-size (vl-packeddimensionlist-total-size x.pdims)))
           (if (and udim-size pdim-size)
               (case x.name
                 ;; See SystemVerilog-2012 Section 6.11, Integer Data Types.

                 ;; integer atom types -- these don't have any dimensions, they're just fixed sizes
                 (:vl-byte     (success (* pdim-size udim-size 8)))
                 (:vl-shortint (success (* pdim-size udim-size 16)))
                 (:vl-int      (success (* pdim-size udim-size 32)))
                 (:vl-longint  (success (* pdim-size udim-size 64)))
                 (:vl-integer  (success (* pdim-size udim-size 32)))
                 (:vl-time     (success (* pdim-size udim-size 64)))

                 ;; integer vector types -- these have arbitrary packed dimensions.
                 ((:vl-bit :vl-logic :vl-reg)
                  (success (* udim-size pdim-size)))

                 (otherwise
                  ;; Something like a real, shortreal, void, realtime, chandle, etc.
                  ;; We don't try to size these, but we still claim success: these just
                  ;; don't have ranges.
                  (fail "bad coretype ~a0" (list x))))
             (fail "Dimensions of vector type ~a0 not resolvd"
                   (list x)))))

        (:vl-struct
         (b* (;; bozo is there a correct thing to do for a struct with no members?
              ((unless (consp x.members)) (fail "empty struct: ~a0" (list x)))
              ((mv warning widths) (vl-structmemberlist-sizes x.members))
              ((when warning) (mv warning nil))
              (packedsize (vl-packeddimensionlist-total-size x.pdims))
              (unpackedsize (vl-packeddimensionlist-total-size x.udims))
              ((unless (and packedsize unpackedsize))
               (fail "Dimensions of struct type ~a0 not resolvd"
                     (list x))))
           (success (* packedsize unpackedsize (sum-nats widths)))))

        (:vl-union
         (b* (;; bozo is there a correct thing to do for a union with no members?
              ((unless (consp x.members)) (fail "empty union: ~a0" (list x)))
              ((mv warning widths) (vl-structmemberlist-sizes x.members))
              ((when warning) (mv warning nil))
              (packedsize (vl-packeddimensionlist-total-size x.pdims))
              (unpackedsize (vl-packeddimensionlist-total-size x.udims))
              ((unless (and packedsize unpackedsize))
               (fail "Dimensions of union type ~a0 not resolvd"
                     (list x))))
           (success (* packedsize unpackedsize (max-nats widths)))))

        (:vl-enum ;; need to compute size from the base type?
         (fail "bozo: implement enum range" nil))

        (:vl-usertype
         (fail "unresolved usertype: ~a0" (list x.kind))))))

  (define vl-structmemberlist-sizes ((x vl-structmemberlist-p))
    :returns (mv (warning (iff (vl-warning-p warning) warning))
                 (sizes   (and (pos-listp sizes)
                               (implies (not warning)
                                        (equal (consp sizes) (consp x))))))
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x)) (mv nil nil))
         ((vl-structmember first) (vl-structmember-fix (car x)))
         ((mv warning size) (vl-datatype-size first.type))
         ((when warning) (mv warning nil))
         ((mv warning rest) (vl-structmemberlist-sizes (cdr x)))
         ((when warning) (mv warning nil)))
      (mv nil (cons size rest))))
  ///
  (defthm-vl-datatype-size-flag
    (defthm len-of-vl-structmemberlist-sizes
      (b* (((mv warning sizes) (vl-structmemberlist-sizes x)))
        (implies (not warning)
                 (equal (len sizes) (len x))))
      :flag vl-structmemberlist-sizes)
    :skip-others t)

  (local (defthm nat-listp-when-pos-listp
           (implies (pos-listp x)
                    (nat-listp x))
           :hints(("Goal" :in-theory (enable nat-listp)))))

  (verify-guards vl-datatype-size)

  (deffixequiv-mutual vl-datatype-size))



(define vl-datatype-set-unsigned ((x vl-datatype-p))
  :returns (new-x vl-datatype-p)
  (vl-datatype-case x
    :vl-coretype (mbe :logic (change-vl-coretype x :signedp nil)
                      :exec (if x.signedp (change-vl-coretype x :signedp nil) x))
    :vl-struct   (mbe :logic (change-vl-struct   x :signedp nil)
                      :exec (if x.signedp (change-vl-struct   x :signedp nil) x))
    :vl-union    (mbe :logic (change-vl-union    x :signedp nil)
                      :exec (if x.signedp (change-vl-union    x :signedp nil) x))
    :otherwise   (vl-datatype-fix x)))

#||

(trace$
 #!VL (vl-datatype-exprtype
       :entry (list* 'vl-datatype-exprtype
                     x
                     (with-local-ps (vl-pp-datatype x))
                     (and (eq (vl-datatype-kind x) :vl-coretype)
                          (list :name (vl-coretype->name x)
                                :signedp (vl-coretype->signedp x))))
       :exit (cons 'vl-datatype-exprtype
                   (b* (((mv & err type) values))
                     (if err
                         (list err)
                       (list :type type))))))

||#


(define vl-datatype-exprtype
  :parents (datatype-tools vl-expr-typedecide)
  :short "Get the self-determined type for a datatype."
  ((x vl-datatype-p))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription
                "NOTE: type may still be NIL on success.")
      (errmsg maybe-stringp :rule-classes :type-prescription
              "On failure: a very brief explanation of the failure reason.")
      (type vl-maybe-exprtype-p
            "On success: the self-determined type of this expression.  Note
             that some expressions (e.g., real numbers) have type NIL."))
  :long "<p>BOZO we don't try very hard yet.  Eventually this will need to know
         how to look up the sizes of user-defined types, etc.</p>

        <p>BOZO At the moment we treat unpacked stuff just like packed stuff,
        and there's not much error checking for using unpacked stuff improperly.</p>"
  (b* (((fun (fail reason))   (mv nil reason nil))
       ((fun (success width)) (mv t nil width))
       ((when (consp (vl-datatype->udims x)))
        ;; (fail "Can't decide signedness of unpacked array")
        ;; Can we just say unpacked stuff is always unsigned?
        (success :vl-unsigned)
        ))
    (vl-datatype-case x

      (:vl-coretype
       (case x.name
         ((:vl-byte :vl-shortint :vl-int :vl-longint :vl-integer :vl-time
           :vl-bit :vl-logic :vl-reg)
          ;; See also vl-parse-core-data-type.  When using any of the above
          ;; types, a logic designer can provide an optional `signed` or
          ;; `unsigned` keyword that, presumably, overrides the default
          ;; signedness.  The parser handles this and must set up the
          ;; coretype.signedp field appropriately.  So, here, we just need to
          ;; look at that field.
          (success (if x.signedp :vl-signed :vl-unsigned)))

         (otherwise
          ;; Some other kind of core type like void, string, chandle, event,
          ;; or similar.  We're not going to assign any type to these, but
          ;; it's not any kind of error.
          (success nil))))

      (:vl-enum ;; just need to look at the base type, right?
       (fail "bozo: implement enum typing"))

      (:vl-struct ;; just need to look at signedp and packed?
       (b* (((unless x.packedp) ;; (fail "non-packed struct")
             ;; Can we just say unpacked stuff is always unsigned?
             (success :vl-unsigned)))
         (success (if x.signedp :vl-signed :vl-unsigned))))

      (:vl-union ;; just need to look at signedp and packed?
       (b* (((unless x.packedp) ;; (fail "non-packed union")
             ;; Can we just say unpacked stuff is always unsigned?
             (success :vl-unsigned)))
         (success (if x.signedp :vl-signed :vl-unsigned))))

      (:vl-usertype
       ;; BOZO maybe some day extend this to be able to do lookups
       (fail "vl-datatype-exprtype can't handle unresolved usertypes")))))


(define vl-datatype-bitselect-ok ((x vl-datatype-p))
  :returns (okp)
  :parents (datatype-tools)
  :short "Determines whether this datatype can be bitselected."
  :long "<p>The input datatype should not have packed or unpacked dimensions;
if it does, then it's definitely OK to index into it (though it's only a
bitselect if it's the last packed dimension).  The input datatype should have
usertypes resolved.</p>"
  :guard (and (not (consp (vl-datatype->pdims x)))
              (not (consp (vl-datatype->udims x))))
  (vl-datatype-case x
    (:vl-coretype
     (b* (((vl-coredatatype-info xinfo) (vl-coretypename->info x.name)))
       ;; Checks whether this is an integer atom type.  If it's an integer
       ;; vector type, it's only selectable if it has dims.
       (and xinfo.size (not (eql xinfo.size 1)))))
    (:vl-struct x.packedp)
    (:vl-union  x.packedp)
    (:vl-enum   nil) ;; BOZO is this correct?
    (:vl-usertype nil)))



