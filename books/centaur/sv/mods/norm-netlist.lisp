; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2023 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "lhs")
(local (include-book "std/alists/fast-alist-clean" :dir :system))
(local (std::add-default-post-define-hook :Fix))

;; This is an updated algorithm for netlist normalization.  More specifically,
;; this takes a flattened, alias-normalized netlist (assigns-p -- mapping LHS
;; to driver) and returns an svex-alist mapping every variable mentioned in one
;; of the LHSes of the assigns to a full local assignment.

;; The old implementation of this was two steps: collect all the drivers for
;; each variable, then resolve them into a single driving assignment.  When
;; collecting the drivers, the original drivers were each applied to only a
;; segment of the variable, so we would extend them with Zs in the undriven
;; parts.

;; The new implementation is similar except that we keep explicit the segment
;; that each driver is applied to.  We then create concatenations directly for
;; the common case where drivers don't overlap, instead of producing a RES
;; function by default.

(defprod segment-driver
  ((lsb natp :rule-classes :type-prescription)
   (width posp :rule-classes :type-prescription)
   (value svex)
   (strength natp :default 6 :rule-classes :type-prescription))
  :layout :tree)

(deflist segment-driverlist :elt-type segment-driver :true-listp t :elementp-of-nil nil)

(fty::defmap segment-driver-map :key-type svar :val-type segment-driverlist
  ///
  (defthm segment-driver-map-p-of-hons-remove-assoc
    (implies (segment-driver-map-p x)
             (segment-driver-map-p (acl2::hons-remove-assoc k x)))
    :hints(("Goal" :in-theory (enable segment-driver-map-p acl2::hons-remove-assoc))))
  (defthm segment-driver-map-p-of-fast-alist-clean
    (implies (segment-driver-map-p x)
             (segment-driver-map-p (fast-alist-clean x)))
    :hints(("Goal" :in-theory (e/d (acl2::fast-alist-clean-by-remove-assoc)
                                   (acl2::fast-alist-clean))))))




(define segment-driver-vars ((x segment-driver-p))
  :returns (vars svarlist-p)
  (svex-vars (segment-driver->value x)))

(define segment-driverlist-vars ((x segment-driverlist-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (append (segment-driver-vars (car x))
            (segment-driverlist-vars (cdr x)))))

(define segment-driver-map-vars ((x segment-driver-map-p))
  :measure (len x)
  :returns (vars svarlist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (segment-driver-map-vars (cdr x))))
    (cons (caar x)
          (append (segment-driverlist-vars (cdar x))
                  (segment-driver-map-vars (cdr x)))))
  ///
  (deffixequiv segment-driver-map-vars
    :hints(("Goal" :in-theory (enable segment-driver-map-fix))))
  (defthm segment-driver-map-vars-of-acons
    (equal (segment-driver-map-vars (cons (cons a b) c))
           (if (svar-p a)
               (cons (svar-fix a)
                     (append (segment-driverlist-vars b)
                             (segment-driver-map-vars c)))
             (segment-driver-map-vars c)))
    :hints(("Goal" :in-theory (enable segment-driver-map-fix))))

  (defthm segment-driver-map-vars-of-append
    (equal (segment-driver-map-vars (append a b))
           (append (segment-driver-map-vars a)
                   (segment-driver-map-vars b)))
  :hints(("Goal" :in-theory (enable segment-driver-map-vars segment-driver-map-fix append)
          :induct (segment-driver-map-vars a)
          :expand ((:free (a b) (segment-driver-map-vars (cons a b)))
                   (append a b)))))

  (defthm member-lookup-in-segment-driver-map
    (implies (and (not (member v (segment-driver-map-vars x)))
                  (svar-p name))
             (not (member v (segment-driverlist-vars (cdr (hons-assoc-equal name x))))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthm segment-driver-map-vars-of-remove-assoc
    (implies (and (not (member v (segment-driver-map-vars x)))
                  (segment-driver-map-p x))
             (not (member v (segment-driver-map-vars (acl2::hons-remove-assoc k x)))))
    :hints(("Goal" :in-theory (enable acl2::hons-remove-assoc))))

  (defthm segment-driver-map-vars-of-fast-alist-clean
    (implies (and (not (member v (segment-driver-map-vars x)))
                  (segment-driver-map-p x))
             (not (member v (segment-driver-map-vars (fast-alist-clean x)))))
    :hints(("Goal" :in-theory (e/d (acl2::fast-alist-clean-by-remove-assoc)
                                   (acl2::fast-alist-clean))))))



(define assign->segment-drivers ((lhs lhs-p) (offset natp) (dr driver-p)
                                 (acc segment-driver-map-p "accumulator"))
  :parents (svex-compilation)
  :short "From an assignment to an LHS, accumulate the segment-drivers for each variable mentioned."
  :long "

<p>For example, suppose we have the following Verilog code:</p>

@({
 wire [10:0] a;
 wire [8:1] b;
 wire [3:2] c;
 wire [12:0] foo;
 assign { a[8:3], b[5:1], c } = foo;
 })

<p>We split this assignment into three separate assignments like this:</p>

@({
 assign a[8:3] = foo[12:7];
 assign b[5:1] = foo[6:2];
 assign c[3:2] = foo[1:0];
 })

<p>Then we accumulate the assignments for a, b, and c onto lists of collected
assignments for each one.  The representation for each such assignment is a
@(see segment-driver) which gives the range of the LHS variable that is
assigned, the expression to be assigned to it, and the drive strength.  These
are collected for each LHS variable into a mapping from the LHS variables to
their list of segment drivers.</p>"
  :returns (assigns segment-driver-map-p)
  :measure (len lhs)
  (b* (((mv first rest) (lhs-decomp lhs))
       (acc (segment-driver-map-fix acc))
       ((unless first) acc)
       ((lhrange first) first)
       (offset (lnfix offset))
       ((when (eq (lhatom-kind first.atom) :z))
        (assign->segment-drivers rest (+ offset first.w) dr acc))
       ((lhatom-var first.atom))
       ((driver dr))
       (new-driver (make-segment-driver
                    :value (svex-rsh offset dr.value)
                    :strength dr.strength
                    :lsb first.atom.rsh
                    :width first.w))
       (rest-drivers (cdr (hons-get first.atom.name acc)))
       (acc (hons-acons first.atom.name (cons new-driver rest-drivers) acc)))
    (assign->segment-drivers rest (+ offset first.w) dr acc))
  ///
  (deffixequiv assign->segment-drivers)

  (defthm vars-of-assign->segment-drivers
    (implies (and (not (member v (lhs-vars lhs)))
                  (not (member v (svex-vars (driver->value dr))))
                  (not (member v (segment-driver-map-vars acc))))
             (not (member v (segment-driver-map-vars (assign->segment-drivers lhs offset dr acc)))))
    :hints (("goal" :induct (assign->segment-drivers lhs offset dr acc)
             :expand ((lhs-vars lhs)
                      (:free (a b) (segment-driverlist-vars (cons a b)))
                      (:free (lsb w value str) (segment-driver-vars (segment-driver lsb w value str)))
                      (:free (v a b)(member-equal v (cons a b))))
             :in-theory (enable svex-alist-vars lhatom-vars))))
  
  
  (defthm hons-assoc-equal-of-assign->segment-drivers
    (implies (and (not (member v (lhs-vars lhs)))
                  (not (hons-assoc-equal v (segment-driver-map-fix acc))))
             (not (hons-assoc-equal v (assign->segment-drivers lhs offset dr acc))))
    :hints (("goal" :induct (assign->segment-drivers lhs offset dr acc)
             :expand ((lhs-vars lhs))
             :in-theory (enable svex-alist-vars lhatom-vars)))))





(define assigns->segment-drivers-aux ((x assigns-p) (acc segment-driver-map-p))
  :measure (len (assigns-fix x))
  :returns (segment-driver-map segment-driver-map-p)
  (b* ((x (assigns-fix x))
       (acc (segment-driver-map-fix acc))
       ((when (atom x)) acc))
    (assigns->segment-drivers-aux (cdr x)
                             (assign->segment-drivers (caar x) 0 (cdar x) acc)))
  ///
  (defthm vars-of-assigns->segment-drivers-aux
    (implies (and (not (member v (assigns-vars x)))
                  (not (member v (segment-driver-map-vars acc))))
             (not (member v (segment-driver-map-vars (assigns->segment-drivers-aux x acc)))))
    :hints (("goal" :induct (assigns->segment-drivers-aux x acc)
             :expand ((assigns-vars x)))))
  

  (defthm hons-assoc-equal-of-assigns->segment-drivers-aux
    (implies (and (not (member v (assigns-vars x)))
                  (not (hons-assoc-equal v (segment-driver-map-fix acc))))
             (not (hons-assoc-equal v (assigns->segment-drivers-aux x acc))))
    :hints (("goal" :induct (assigns->segment-drivers-aux x acc)
             :expand ((assigns-vars x))))))

(define assigns->segment-drivers ((x assigns-p))
  :parents (svex-compilation)
  :short "For a list of assignments of driving expressions to LHSes, produce an
alist mapping each variable from the LHSes to the full list of segment drivers
for that variable."
  :returns (segment-driver-map segment-driver-map-p)
  (fast-alist-free (fast-alist-clean (assigns->segment-drivers-aux x nil)))
  ///
  (defthm vars-of-assigns->segment-drivers
    (implies (not (member v (assigns-vars x)))
             (not (member v (segment-driver-map-vars (assigns->segment-drivers x)))))
    :hints(("Goal" :in-theory (disable fast-alist-clean))))

  (defthm hons-assoc-equal-of-assigns->segment-drivers
    (implies (not (member v (assigns-vars x)))
             (not (hons-assoc-equal v (assigns->segment-drivers x))))))


;; To resolve a list of segment-drivers into a single assignment:
;;  - Sort the segment-drivers
;;  - Transform them into a disjoint, ordered list by resolving all overlapping parts according to drive strength
;;  - Turn the disjoint, ordered list into an svex concatenation.

(define segment-drivers-disjoint-p ((x segment-driverlist-p))
  (b* (((when (atom (cdr x))) t)
       ((segment-driver x1) (car x))
       ((segment-driver x2) (cadr x)))
    (and (<= (+ x1.lsb x1.width) x2.lsb)
         (segment-drivers-disjoint-p (cdr x)))))

(define disjoint-segment-drivers->svex ((x segment-driverlist-p))
  :guard (segment-drivers-disjoint-p x)
  :returns (svex svex-p)
  :verify-guards nil
  (b* (((when (atom (cdr x)))
        (if (atom x)
            (svex-z)
          (b* (((segment-driver x1) (car x)))
            (svex-concat x1.width x1.value (svex-z)))))
       ((segment-driver x1) (car x))
       ((segment-driver x2) (cadr x))
       (msbs (disjoint-segment-drivers->svex (cdr x)))
       ((when (eql (+ x1.lsb x1.width) x2.lsb))
        (svex-concat x1.width x1.value msbs)))
    (svex-concat x1.width x1.value
                 (svex-concat (- x2.lsb (+ x1.lsb x1.width)) (svex-z) msbs)))
  ///
  (verify-guards disjoint-segment-drivers->svex
    :hints (("goal" :in-theory (enable segment-drivers-disjoint-p))))

  (defret vars-of-<fn>
    (implies (not (member-equal v (segment-driverlist-vars x)))
             (not (member-equal v (svex-vars svex))))
    :hints(("Goal" :in-theory (enable segment-driverlist-vars
                                      segment-driver-vars)))))





;; Sort by lsb (increasing), then width (increasing).
(define segment-driver-< ((x segment-driver-p)
                          (y segment-driver-p))
  (b* (((segment-driver x))
       ((segment-driver y)))
    (or (< x.lsb y.lsb)
        (and (eql x.lsb y.lsb)
             (< x.width y.width))))
  ///
  (acl2::defsort segment-drivers-sort
    :prefix segment-drivers
    :comparablep segment-driver-p
    :comparable-listp segment-driverlist-p
    :true-listp t
    :compare< segment-driver-<))

(deffixequiv segment-drivers-ordered-p
  :hints(("Goal" :in-theory (enable segment-drivers-ordered-p)))
  :args ((x segment-driverlist)))

(define segment-driverlist-chunk-width ((lsb natp)
                                        (x segment-driverlist-p))
  :guard (segment-drivers-ordered-p x)
  ;; If we return NIL, it means all segments had (<= (+ x1.lsb x1.width) lsb),
  ;; i.e. they end before we begin.
  :returns (width maybe-posp :rule-classes :type-prescription)
  :verify-guards nil
  (b* (((when (atom x)) nil)
       ((segment-driver x1) (car x))
       ;; We don't need to look any further if x1.lsb > lsb, because the
       ;; drivers are ordered by LSB and so this one gives us the smallest
       ;; chunk of the rest.
       ((when (> x1.lsb (lnfix lsb)))
        (- x1.lsb (lnfix lsb)))
       ;; If x1.lsb+x1.width <= lsb, we can ignore x1.
       ;; (Note the bits included are [ x1.lsb, x1.lsb+width-1 ].)
       ((when (<= (+ x1.lsb x1.width) (lnfix lsb)))
        (segment-driverlist-chunk-width lsb (cdr x)))
       (rest (segment-driverlist-chunk-width lsb (cdr x)))
       (x1-chunk-width (- (+ x1.lsb x1.width) (lnfix lsb))))
    (if (and rest
             (< rest x1-chunk-width))
        rest
      x1-chunk-width))
  ///
  (verify-guards segment-driverlist-chunk-width
    :hints(("Goal" :in-theory (enable segment-drivers-ordered-p)))))


(define segment-driverlist-collect-chunk ((lsb natp)
                                          (width posp)
                                          (x segment-driverlist-p))
  :returns (chunk driverlist-p)
  :guard (segment-drivers-ordered-p x)
  :verify-guards nil
  :measure (len x)
  (b* (((when (atom x)) nil)
       (lsb (lnfix lsb))
       (width (lposfix width))
       ((segment-driver x1) (car x))
       ;; Because the chunk stops at the minimum greater LSB as well as minimum
       ;; MSB, if x1.lsb > lsb, then x1.lsb+x1.width >= lsb and we can ignore
       ;; this chunk and (because sorted) all the rest.
       ((when (< lsb x1.lsb)) nil)
       ((when (<= (+ x1.lsb x1.width) lsb))
        (segment-driverlist-collect-chunk lsb width (cdr x))))
    (cons (make-driver
           :value (svex-rsh (- lsb x1.lsb) x1.value)
           :strength x1.strength)
          (segment-driverlist-collect-chunk lsb width (cdr x))))
  ///
  (verify-guards segment-driverlist-collect-chunk
    :hints(("Goal" :in-theory (enable segment-drivers-ordered-p))))

  (defret vars-of-<fn>
    (implies (not (member-equal v (segment-driverlist-vars x)))
             (not (member-equal v (driverlist-vars chunk))))
    :hints(("Goal" :in-theory (enable segment-driverlist-vars
                                      segment-driver-vars)))))
          

(define segment-driverlist-chunk-tail ((next-lsb natp)
                                       (x segment-driverlist-p))
  :guard (segment-drivers-ordered-p x)
  :guard-hints (("goal" :in-theory (enable segment-drivers-ordered-p)))
  :returns (tail segment-driverlist-p)
  (b* (((when (atom x)) nil)
       ((segment-driver x1) (car x))
       ((when (<= (+ x1.lsb x1.width) (lnfix next-lsb)))
        (segment-driverlist-chunk-tail next-lsb (cdr x))))
    (segment-driverlist-fix x))
  ///

  (defret <fn>-len-decr-unless-lsb-plus-width-greater
    (implies (and (consp x)
                  (case-split
                    (b* (((segment-driver x1) (car x)))
                      (<= (+ x1.lsb x1.width) (nfix next-lsb)))))
             (< (len tail) (len x)))
    :rule-classes :linear)

  (defret <fn>-non-incr
    (<= (len tail) (len x))
    :rule-classes :linear)

  (defret <fn>-car
    (implies (and (equal (len (segment-driverlist-chunk-tail next-lsb x)) (len x))
                  (consp x))
             (equal (car tail) (segment-driver-fix (car x)))))

  (defret segment-drivers-ordered-p-of-<fn>
    (implies (segment-drivers-ordered-p x)
             (segment-drivers-ordered-p tail))
    :hints(("Goal" :in-theory (enable segment-drivers-ordered-p))))

  (defret vars-of-<fn>
    (implies (not (member-equal v (segment-driverlist-vars x)))
             (not (member-equal v (segment-driverlist-vars tail))))
    :hints(("Goal" :in-theory (enable segment-driverlist-vars)))))
    

(define segment-driverlist-deoverlap ((lsb natp)
                                      (x segment-driverlist-p))
  :parents (segment-driverlist-resolve)
  :short "Resolve overlapping elements of an ordered list of segment driver
objects, resulting in an ordered, nonoverlapping list."
  :long "<p> We iterate from LSB=0, at each iteration finding the biggest chunk
starting at the current LSB such that there are no segment boundaries inside
the chunk, then incrementing LSB by that chunk size for the next iteration.</p>

<p>The ordering of the driverlist, sorted by increasing LSB then increasing
width, usually allows us to throw out a prefix of the list whenever we incrase
the LSB, since any segments that end before the current LSB are no longer
relevant.</p>

<p>At each iteration, we first find the chunk width by taking the minimum of
all segment endpoints greater than the current LSB, minus the LSB.  Then we
collect all drivers that overlap with the chunk between LSB and LSB+width-1,
sort them by drive strength, and resolve them together to create one driver for
that segment. The next LSB is then LSB+width, and we discard any leading
elements of the segment list whose segments end before that point.</p>"
  :guard (segment-drivers-ordered-p x)
  :returns (new-x segment-driverlist-p)
  :measure (acl2::two-nats-measure (len x)
                                   (b* (((segment-driver x1) (car x)))
                                     (nfix (- (+ x1.lsb x1.width) (nfix lsb)))))
  :prepwork ((local (defthm nfix-bound-when-integerp
                      (implies (integerp x)
                               (<= x (nfix x)))
                      :hints(("Goal" :in-theory (enable nfix)))
                      :rule-classes :linear)))
  ;; :hints ((and stable-under-simplificationp
  ;;              '(:in-theory (enable nfix))))
  (b* (((when (atom x)) nil)
       ;; The chunk we are now concerned with goes from lsb to the minimum of
       ;; all xi.lsb and xi.lsb+xi.width, but discarding those <= lsb.  We
       ;; first find this chunk width, then scan through the list to find
       ;; drivers that overlap it.  There should be no partial overlaps.
       (width (segment-driverlist-chunk-width lsb x))
       ((unless width)
        ;; width is nil means all segments are before LSB, so we're done.
        nil)
       (drivers (segment-driverlist-collect-chunk lsb width x))
       (value (driverlist->svex (drivestrength-sort drivers)))
       (next-lsb (+ width (lnfix lsb)))
       (tail (segment-driverlist-chunk-tail next-lsb x)))
    (cons (make-segment-driver :lsb lsb :width width
                               :value value) ;; strength doesn't matter anymore
          (segment-driverlist-deoverlap next-lsb tail)))
  ///
  (defret lsb-car-of-<fn>
    (implies (consp new-x)
             (equal (segment-driver->lsb (car new-x))
                    (nfix lsb))))
  (defret segment-drivers-disjoint-p-of-<fn>
    (segment-drivers-disjoint-p new-x)
    :hints(("Goal" :in-theory (enable segment-drivers-disjoint-p))))

  (defret vars-of-<fn>
    (implies (not (member-equal v (segment-driverlist-vars x)))
             (not (member-equal v (segment-driverlist-vars new-x))))
    :hints(("Goal" :in-theory (enable segment-driverlist-vars
                                      segment-driver-vars)))))
    

(define segment-driverlist-resolve ((x segment-driverlist-p))
  :parents (segment-driver-map-resolve)
  :short "Given the list of drivers for various segments of a variable, turn
them into a single svex comprising that variable's full assignment."
  :long " <p>This works in three main steps: sort the drivers by LSB and width,
resolve each overlap of multiple drivers into a combined driver so that all
drivers are nonoverlapping, and finally concatenate the value expressions of
this nonoverlapping list of drivers into a single expression.</p>

<p>The complicated part is resolving overlapping drivers; see @(see
segment-driverlist-deoverlap).</p>"
  :returns (value svex-p)
  (b* ((sort (segment-drivers-sort (segment-driverlist-fix x)))
       (deoverlap (segment-driverlist-deoverlap 0 sort)))
    (disjoint-segment-drivers->svex deoverlap))
  ///
  (defthm vars-of-segment-drivers-insert
    (implies (and (not (member-equal v (segment-driver-vars elt)))
                  (not (member-equal v (segment-driverlist-vars x))))
             (not (member-equal v (segment-driverlist-vars (segment-drivers-insert elt x)))))
    :hints(("Goal" :in-theory (enable segment-drivers-insert
                                      segment-driverlist-vars))))

  (defthm vars-of-segment-drivers-insertsort
    (implies (and (not (member-equal v (segment-driverlist-vars x))))
             (not (member-equal v (segment-driverlist-vars (segment-drivers-insertsort x)))))
    :hints(("Goal" :in-theory (enable segment-drivers-insertsort
                                      segment-driverlist-vars))))

  (defret vars-of-<fn>
    (implies (not (member-equal v (segment-driverlist-vars x)))
             (not (member-equal v (svex-vars value))))))




(assert-event
 (equal (segment-driverlist-resolve
         (list (make-segment-driver :lsb 4 :width 5 :value 'y)
               (make-segment-driver :lsb 2 :width 5 :value 'x)))
        '(CONCAT 2 (0 . -1)
                 (CONCAT 2 X
                         (CONCAT 3 (RES (RSH 2 X) Y)
                                 (concat 2 (RSH 3 Y) (0 . -1)))))))

(assert-event
 (equal (segment-driverlist-resolve
         (list (make-segment-driver :lsb 8 :width 5 :value 'y)
               (make-segment-driver :lsb 0 :width 5 :value 'x)))
        '(CONCAT 5 X (CONCAT 3 (0 . -1)
                             (concat 5 Y (0 . -1))))))

;; add more tests...




(define segment-driver-map-resolve-nrev ((x segment-driver-map-p) (nrev))
  :measure (len x)
  (b* (((when (atom x)) (acl2::nrev-fix nrev))
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (segment-driver-map-resolve-nrev (cdr x) nrev))
       ((cons name drivers) (car x))
       (value (segment-driverlist-resolve drivers))
       (nrev (acl2::nrev-push (cons name value) nrev)))
    (segment-driver-map-resolve-nrev (cdr x) nrev))
  ///
  (local (in-theory (enable segment-driver-map-fix))))


(local (include-book "std/lists/sets" :dir :system))

(define segment-driver-map-resolve ((x segment-driver-map-p))
  :parents (svex-compilation)
  :short "Given an alist mapping each driven variable to its list of segment
drivers, resolve this to an svex-alist mapping each variable to its full
assignment."
  :long " <p>This applies @(see segment-driverlist-resolve) to the list of
drivers for each variable.</p> "
  :measure (len x)
  :returns (assigns svex-alist-p)
  :verify-guards nil
  (mbe :logic
       (b* (((when (atom x)) nil)
            ((unless (mbt (and (consp (car x))
                               (svar-p (caar x)))))
             (segment-driver-map-resolve (cdr x)))
            ((cons name drivers) (car x))
            (value (segment-driverlist-resolve drivers)))
         (cons (cons name value)
               (segment-driver-map-resolve (cdr x))))
       :exec
       (if (atom x)
           nil
         (acl2::with-local-nrev
           (segment-driver-map-resolve-nrev x acl2::nrev))))
  ///
  (local (defthm segment-driver-map-resolve-nrev-elim
           (equal (segment-driver-map-resolve-nrev x nrev)
                  (append nrev (segment-driver-map-resolve x)))
           :hints(("Goal" :in-theory (enable segment-driver-map-resolve-nrev
                                             acl2::rcons)))))

  (verify-guards segment-driver-map-resolve)

  (defthm vars-of-segment-driver-map-resolve
    (implies (not (member v (segment-driver-map-vars x)))
             (and (not (member v (svex-alist-keys (segment-driver-map-resolve x))))
                  (not (member v (svex-alist-vars (segment-driver-map-resolve x))))))
    :hints(("Goal" :in-theory (e/d (segment-driver-map-vars svex-alist-vars svex-alist-keys)
                                   (member-svex-alist-keys)))))

  (defret svex-lookup-under-iff-of-<fn>
    (iff (svex-lookup v assigns)
         (hons-assoc-equal (svar-fix v) (segment-driver-map-fix x)))
    :hints(("Goal" :in-theory (enable segment-driver-map-fix svex-lookup))))

  (local (in-theory (enable segment-driver-map-fix))))
