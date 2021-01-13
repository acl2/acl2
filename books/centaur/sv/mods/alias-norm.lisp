; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "lhs")
(include-book "../svex/constraints")
(include-book "std/basic/two-nats-measure" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (in-theory (disable nth update-nth acl2::nth-when-zp)))

;; [Jared] getting build failures in ( VERIFY-GUARDS LHS-PAIRS-SET-ALIASES ...)
;; regarding (REALP (LHRANGE->W (CAR (LHS-NORM Y)))), so just disabling this on
;; ACL2(r) for now:

;; cert_param: (non-acl2r)

(defxdoc alias-normalization
  :parents (svex-compilation)
  :short "The process of computing a canonical form for each wire in the module hierarchy."
  :long "<p>Alias normalization takes as input a list of pairs of @(see lhs)
objects and computes a canonical form for each wire mentioned.  The inputs must
be in indexed-variable form; that is, each variable name must be a unique
natural number (this allows us to use arrays to look up variable
properties).</p>

<p>The normalization algorithm is similar to a disjoint sets union-find
algorithm.  Initially, every wire is mapped to itself.  For each alias pair, we
canonicalize the two LHS objects according to our current mapping.  That is,
for each wire range in the LHS, we look up the current mapping of the wire,
truncate it to the relevant range, and recursively canonicalize that, stopping
on ranges that are mapped to themselves.  (In order that this process
terminates, it is an invariant that every subrange of every wire is mapped to a
range of a wire whose index is less than or equal to the index of that wire;
and if mapped to itself, then to either a lower range of bits or just to
itself.)</p>

<p>Then, when we have normalized the two LHSes, we break this pairing down into
pairs of single wire ranges.  For example, if our two normalized LHSes are @('{
a[5:4], b[7:3] }') and @('{ c[8:5], d[9:7] }'), these would be broken down into
the pairs:</p>
@({ (a[5:4], c[8:7]),
    (b[7:6], c[6:5]),
    (b[5:3], d[9:7]). })

<p>For each of these range pairs, unless the two elements are the same, we set
the canonical version of one to the other, chosen so that the ordering
invariant is maintained.</p>

<p>To finish processing the current alias pair, we again recursively
canonicalize the original pair of LHS objects.  However, now, whenever we find
the canonical version of a wire range, we replace the mapping for that wire
range with the canonical version found.  As in the union-find algorithm, this
is a performance optimization to minimize the number of steps necessary in
future searches.</p>

<p>Once all alias pairs are processed like this, we finish by doing a linear
sweep over all entries in the table, replacing every wire range by its
canonical representation.</p>

<h5>Correctness of the algorithm</h5>

<p>We haven't proved the algorithm correct.  Here are some thoughts on the topic.</p>

<p>The correctness statement is something like the following.</p>

<p>If v and w are each a bit selected from some wire, then @('canon(v) =
canon(w)') iff there exists a path @('v0, ..., vn') where:</p>
<ul>
<li>@('v0 = v') and @('vn = w')</li>
<li>for all @('i') from 0 to @('n-1'), there exists an alias pair such that
@('vi') and @('vi+1') are corresponding bits in the two LHS objects of the
pair.</li>
</ul>

<p>During the main loop of the algorithm (i.e. between processing alias pairs),
this property holds of the alias pairs processed so far, if we regard
@('canon(v)') as recursive canonicalization of @('v') as opposed to a single
lookup.  Inductive argument:</p>

<p>Base case: we haven't processed any alias pairs yet; by the initial setting
of the mapping, @('canon(v) = canon(w)') iff @('v == w').</p>

<p>Inductive case: Suppose the property holds before adding an alias pair, and
show it holds after adding it.</p>

<p>Backward direction: Show that if a path exists from v to w, then the
canonical forms are equal.</p>

<p>Lemma: If @('canon(v) = canon(w)') before, then this is true after.  We only
change the mapping for values that are canonical, which only adds
equivalences (unions sets), or for non-canonical values by replacing their
mapping with their canonical values, which preserves equivalences.</p>

<p>So if the path exists without our new alias pair, then by I.H. the canonical
forms are equal before, so they are equal after as well.  So we only need to
consider the case where the path uses our new alias pair.  Basically, it
suffices to show that as we process the alias pair, we equalize the canonical
forms of corresponding bits.  So since each link in the path is corresponding
bits of a pair, they have equal canonical representations.</p>

<p>Forward direction: If there is no path, then the canonical forms differ.  To
prove this, we assume the canonical forms are the same and produce a path.  We
only need to consider v, w whose canonical forms are newly equal: if they were
equal before then there was a path before by IH, and that same path works now.
The only operation that equalizes new pairs is that we set a canonical range to
the corresponding canonical range of the other LHS.</p>

<p>Lemma: Setting a canonical range to another range only affects the canonical
form of bits whose canonical form was in that range.</p>

<p>Bits whose canonical form was in the changed range (by IH) have a path to
corresponding bits of that range.  The part of the original LHS that mapped to
that range also has such a path.  Concatenate these two, step over the current
alias to some bit whose canonical form already was the new canonical form in
question -- so then concatenate on that bit's path to w.  Got that?</p>")
(defxdoc alias-norm.lisp :parents (alias-normalization))





(local (xdoc::set-default-parents alias-norm.lisp))

(define lhatom-bound-fix ((bound integerp) (offset natp) (x lhatom-p))
  :guard (lhatom-normorderedp bound offset x)
  :returns (xx (and (lhatom-p xx)
                    (lhatom-normorderedp bound offset xx)))
  (mbe :logic (if (lhatom-normorderedp bound offset x)
                  (lhatom-fix x)
                (lhatom-z))
       :exec x)
  ///
  (deffixequiv lhatom-bound-fix)

  (defthm lhatom-bound-fix-when-lhatom-normorderedp
    (implies (lhatom-normorderedp bound offset x)
             (equal (lhatom-bound-fix bound offset x)
                    (lhatom-fix x))))

  (defthm lhatom-bound-fix-forward-to-normorderedp
    (lhatom-normorderedp bound idx (lhatom-bound-fix bound idx x))
    :rule-classes ((:forward-chaining :trigger-terms
                    ((lhatom-bound-fix bound idx x)))))

  (defthm lhatom-vars-of-lhatom-bound-fix
    (implies (not (member v (lhatom-vars x)))
             (not (member v (lhatom-vars (lhatom-bound-fix b o x)))))))

(define lhs-varbound-fix ((bound integerp) (offset natp) (x lhs-p))
  :guard (lhs-vars-normorderedp bound offset x)
  :verify-guards nil
  :returns (xx (and (lhs-p xx)
                    (lhs-vars-normorderedp bound offset xx))
               :hints(("Goal" :in-theory (enable lhs-vars-normorderedp
                                                 lhatom-normorderedp))))
  (mbe :logic
       (if (atom x)
           (lhs-fix x)
         (cons (b* (((lhrange xf) (car x)))
                 (lhrange xf.w (lhatom-bound-fix bound offset xf.atom)))
               (lhs-varbound-fix bound (+ (lnfix offset) (lhrange->w (car x))) (cdr x))))
       :exec x)
  ///
  (defthm lhs-varbound-fix-when-lhs-vars-normorderedp
    (implies (lhs-vars-normorderedp bound offset x)
             (equal (lhs-varbound-fix bound offset x)
                    (lhs-fix x)))
    :hints(("Goal" :in-theory (enable lhs-vars-normorderedp))))
  (verify-guards lhs-varbound-fix)
  (deffixequiv lhs-varbound-fix))


(define aliases-fix (aliases)
  :enabled t
  :inline t
  (mbe :logic (non-exec (lhslist-fix aliases))
       :exec aliases))

(define aliases-bound-fix-aux ((n natp) aliases)
  :guard (and (<= n (aliass-length aliases))
              (aliases-normorderedp-aux n aliases))
  :verify-guards nil
  :returns (aliases1 lhslist-p)
  (if (zp n)
      (aliases-fix aliases)
    (let ((aliases (aliases-bound-fix-aux (1- n) aliases)))
      (set-alias (1- n)
                 (lhs-varbound-fix (1- n) 0 (get-alias (1- n) aliases))
                 aliases)))
  ///
  (defthm len-of-aliases-bound-fix-aux
    (implies (<= n (len aliases))
             (equal (len (aliases-bound-fix-aux n aliases))
                    (len aliases))))

  (defthm nth-of-aliases-bound-fix-aux
    (equal (nth m (aliases-bound-fix-aux n aliases))
           (if (< (nfix m) (nfix n))
               (lhs-varbound-fix (nfix m) 0 (nth m aliases))
             (lhs-fix (nth m aliases)))))

  (local (defthm aliases-normorderedp-aux-of-update-greater
           (implies (<= (nfix n) (nfix m))
                    (equal (aliases-normorderedp-aux
                            n (update-nth m val aliases))
                           (aliases-normorderedp-aux n aliases)))
           :hints(("Goal" :in-theory (enable aliases-normorderedp-aux)))))

  (defthm aliases-normorderedp-aux-of-aliases-bound-fix-aux
    (aliases-normorderedp-aux n (aliases-bound-fix-aux n aliases))
    :hints(("Goal" :in-theory (enable aliases-normorderedp-aux))))

  (local (defthm update-nth-when-val-equal-nth
           (implies (and (equal v (nth n x))
                         (< (nfix n) (len x)))
                    (equal (update-nth n v x) x))
           :hints(("Goal" :in-theory (enable update-nth nth)))))

  (defthm aliases-bound-fix-aux-when-aliases-normorderedp-aux
    (implies (and (aliases-normorderedp-aux n aliases)
                  (<= (nfix n) (len aliases)))
             (equal (aliases-bound-fix-aux n aliases)
                    (lhslist-fix aliases)))
    :hints(("Goal" :in-theory (enable aliases-normorderedp-aux))))

  (verify-guards aliases-bound-fix-aux
    :hints(("Goal" :in-theory (enable aliases-normorderedp-aux-implies-get-alias
                                      aliases-normorderedp-aux))))

  (deffixequiv aliases-bound-fix-aux))

(define aliases-bound-fix ((aliases aliases-normorderedp))
  :prepwork ((local (in-theory (enable aliases-normorderedp))))
  :returns (aliases-fix aliases-normorderedp)
  :inline t
  (mbe :logic (aliases-bound-fix-aux (aliass-length aliases) aliases)
       :exec (aliases-fix aliases))
  ///
  (defthm nth-of-aliases-bound-fix
    (equal (nth n (aliases-bound-fix aliases))
           (lhs-varbound-fix (nfix n) 0 (nth n aliases)))
    :hints (("goal" :cases ((< (nfix n) (len aliases)))
             :expand ((lhs-varbound-fix (nfix n) 0 nil)))))

  (defthm aliases-bound-fix-when-aliases-normorderedp
    (implies (aliases-normorderedp aliases)
             (equal (aliases-bound-fix aliases)
                    aliases)))

  (deffixequiv aliases-bound-fix)

  (defthm len-of-aliases-bound-fix
    (equal (len (aliases-bound-fix aliases))
           (len aliases)))

  (fty::deffixtype aliases-normorderedp :pred aliases-normorderedp :fix aliases-bound-fix
    :equiv aliases-equiv :define t :forward t :executablep nil)

  (local (in-theory (disable aliases-bound-fix)))

  (defrefinement lhslist-equiv aliases-equiv))

(define getalias ((n natp) (aliases aliases-normorderedp))
  :guard (< n (aliass-length aliases))
  :inline t
  :returns (lhs (and (lhs-p lhs)
                     (implies (natp n)
                              (lhs-vars-normorderedp n 0 lhs))))
  (mbe :logic (lhs-varbound-fix (nfix n) 0 (get-alias n aliases))
       :exec (get-alias n aliases))
  ///
  (deffixequiv getalias))

(define setalias ((n natp)
                  (x lhs-p)
                  (aliases aliases-normorderedp))
  :guard (and (lhs-vars-normorderedp n 0 x)
              (< n (aliass-length aliases)))
  :inline t
  :returns (aliases1 aliases-normorderedp)
  (mbe :logic (let ((aliases (aliases-bound-fix aliases)))
                (set-alias n (lhs-varbound-fix (nfix n) 0 x) aliases))
       :exec (set-alias n x aliases))
  ///
  (deffixequiv setalias)

  (defthm len-of-setalias-incr
    (<= (len aliases) (len (setalias n x aliases)))
    :rule-classes :linear)

  (defthm len-of-setalias
    (implies (< (nfix n) (len aliases))
             (equal (len (setalias n x aliases)) (len aliases))))

  (defthmd getalias-of-setalias-split
    (equal (getalias n (setalias m v aliases))
           (if (equal (nfix n) (nfix m))
               (lhs-varbound-fix (nfix n) 0 v)
             (getalias n aliases)))
    :hints(("Goal" :in-theory (enable* getalias
                                       acl2::arith-equiv-forwarding))))

  (local (in-theory (e/d (getalias-of-setalias-split)
                         (getalias setalias))))

  (defthm getalias-of-setalias-same
    (equal (getalias n (setalias n v aliases))
           (lhs-varbound-fix (nfix n) 0 v)))

  (defthm getalias-of-setalias-diff
    (implies (not (equal (nfix n) (nfix m)))
             (equal (getalias n (setalias m v aliases))
                    (getalias n aliases)))))


(local (defthm consp-lhs-norm-implies-consp-x
         (implies (consp (lhs-norm x))
                  (consp x))
         :rule-classes :forward-chaining))

(defthm pos-fix-of-nfix
  (equal (acl2::pos-fix (nfix w))
         (acl2::pos-fix w))
  :hints(("Goal" :in-theory (enable acl2::pos-fix nfix))))


(local (defthm ifix-<=-nfix
         (<= (ifix x) (nfix x))
         :hints(("Goal" :in-theory (enable ifix nfix)))
         :rule-classes :linear))

;; (defthm lhs-boundedp-of-lhs-rest
;;   (implies (lhs-boundedp x bound)
;;            (lhs-boundedp (lhs-rest x) bound))
;;   :hints(("Goal" :in-theory (enable lhs-boundedp lhs-rest))))

;; (defthm lhs-boundedp-of-lhs-cons
;;   (implies (and (lhs-boundedp x bound)
;;                 (or (equal (lhatom-kind (lhrange->atom y)) :z)
;;                     (svar-boundedp (lhatom-var->name (lhrange->atom y)) bound)))
;;            (lhs-boundedp (lhs-cons y x) bound))
;;   :hints(("Goal" :in-theory (enable lhs-cons lhs-boundedp))))

;; (defthm lhs-boundedp-of-lhs-rsh
;;   (implies (lhs-boundedp y bound)
;;            (lhs-boundedp (lhs-rsh n y) bound))
;;   :hints(("Goal" :in-theory (enable lhs-boundedp
;;                                     lhs-rsh))))

;; (defthm lhs-boundedp-of-lhs-concat
;;   (implies (and (lhs-boundedp y bound)
;;                 (lhs-boundedp x bound))
;;            (lhs-boundedp (lhs-concat n x y) bound))
;;   :hints(("Goal" :in-theory (enable lhs-boundedp
;;                                     lhs-concat))))

(defines lhs-alias-canonicalize
  (define lhs-alias-canonicalize ((x lhs-p) (idx natp) (w natp) (offset natp)
                                  (aliases aliases-normorderedp))
    :guard (and (< idx (aliass-length aliases))
                (or (zp w) (lhs-vars-normorderedp idx offset x)))
    :verify-guards nil
    :measure (nat-list-measure (list idx w offset (+ 1 (len x))))
    (b* (((mv first rest) (lhs-decomp x))
         ((unless (and first (posp w))) nil)
         (blockw (min w (lhrange->w first))))
      (lhs-concat blockw
                  (lhrange-alias-canonicalize first idx blockw offset aliases)
                  (lhs-alias-canonicalize rest idx
                                          (- w blockw)
                                          (+ (lnfix offset) blockw)
                                          aliases)))

    :returns (canon (and (lhs-p canon)
                         (implies (natp idx)
                                  (lhs-vars-normorderedp idx offset canon)))
                    :hints ('(:expand ((lhs-alias-canonicalize x idx w offset aliases)
                                       (lhs-vars-normorderedp idx offset nil))))))
  (define lhrange-alias-canonicalize ((x lhrange-p) (idx natp) (w posp) (offset natp)
                                      (aliases aliases-normorderedp))
    :guard (and (< idx (aliass-length aliases))
                (<= w (lhrange->w x))
                (lhatom-normorderedp idx offset (lhrange->atom x)))
    :measure (nat-list-measure (list idx (acl2::pos-fix w) offset 0))
    (b* (((lhrange x) x)
         (x.atom (lhatom-bound-fix (lnfix idx) offset x.atom)))
      (lhatom-case x.atom
        :z nil
        :var (b* ((vidx (svar-index x.atom.name))
                  ((when (and (eql vidx (lnfix idx))
                              (eql x.atom.rsh (lnfix offset))))
                   (list (lhrange w x.atom))))
               (lhs-alias-canonicalize
                (lhs-rsh
                 x.atom.rsh
                 (getalias vidx aliases))
                vidx (mbe :logic (acl2::pos-fix w) :exec w) x.atom.rsh aliases))))


    :returns (canon (and (lhs-p canon)
                         ;; could prove a stronger but uglier thm
                         ;; with (svar-index (lhatom-var->name ...))
                         (implies (natp idx)
                                  (lhs-vars-normorderedp idx offset canon)))
                    :hints ('(:expand ((lhrange-alias-canonicalize x idx w offset aliases)
                                       (:free (offset) (lhs-vars-normorderedp idx offset nil))
                                       (:free (x) (lhs-vars-normorderedp idx offset (list x))))))))
  ///
  (deffixequiv-mutual lhs-alias-canonicalize
    :hints (("goal" :expand ((:free (idx offset w)
                              (lhs-alias-canonicalize
                               x idx w offset aliases))
                             (:free (idx offset w)
                              (lhs-alias-canonicalize
                               (lhs-fix x) idx w offset aliases))
                             (:free (idx offset w)
                              (lhrange-alias-canonicalize
                               x idx w offset aliases))
                             (:free (idx offset w)
                              (lhrange-alias-canonicalize
                               (lhrange-fix x) idx w offset aliases))
                             (lhs-alias-canonicalize
                              x idx w offset (aliases-bound-fix aliases))))))
  (verify-guards lhs-alias-canonicalize
    ; :guard-debug t
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance lhs-vars-normorderedp
                          (bound idx)
                          (x (lhs-norm x))))
                   :in-theory (disable lhs-vars-normorderedp-implies-rest)))))

  (local (defthm-lhs-alias-canonicalize-flag
           (defthm lhs-alias-canonicalize-of-lhs-norm
             (equal (lhs-alias-canonicalize (lhs-norm x) idx w offset aliases)
                    (lhs-alias-canonicalize x idx w offset aliases))
             :hints ('(:expand ((lhs-alias-canonicalize x idx w offset aliases)
                                (lhs-alias-canonicalize (lhs-norm x) idx w offset aliases))))
             :flag lhs-alias-canonicalize)
           :skip-others t))

  (fty::deffixcong lhs-norm-equiv equal (lhs-alias-canonicalize x idx w offset aliases) x
    :hints (("goal" :expand ((lhs-alias-canonicalize x idx w offset aliases)
                             (lhs-alias-canonicalize (lhs-norm x) idx w offset aliases)))))


  (defthm-lhs-alias-canonicalize-flag
    (defthm lhs-alias-canonicalize-of-setalias-greater
      (implies (< (nfix idx) (nfix n))
               (equal (lhs-alias-canonicalize
                       x idx w offset (setalias n v aliases))
                      (lhs-alias-canonicalize x idx w offset aliases)))
      :hints ('(:expand ((:free (aliases) (lhs-alias-canonicalize x idx w offset aliases)))))
      :flag lhs-alias-canonicalize)
    (defthm setalias-greater-of-lhrange-alias-canonicalize
      (implies (< (nfix idx) (nfix n))
               (equal (lhrange-alias-canonicalize
                       x idx w offset (setalias n v aliases))
                      (lhrange-alias-canonicalize x idx w offset aliases)))
      :hints ('(:expand ((:free (aliases) (lhrange-alias-canonicalize x idx w offset aliases)))))
      :flag lhrange-alias-canonicalize))

  (defthm-lhs-alias-canonicalize-flag
    (defthm lhs-boundedp-of-lhs-alias-canonicalize
      (implies (and (< (nfix idx) (len aliases))
                    (not (svar-boundedp v (len aliases))))
               (not (member v
                            (lhs-vars (lhs-alias-canonicalize x idx w offset aliases)))))
      :hints ('(:expand ((:free (aliases) (lhs-alias-canonicalize x idx w offset aliases))
                         (lhs-vars nil))))
      :flag lhs-alias-canonicalize)
    (defthm lhs-boundedp-of-lhrange-alias-canonicalize
      (implies (and (< (nfix idx) (len aliases))
                    (not (svar-boundedp v (len aliases))))
               (not (member v
                            (lhs-vars (lhrange-alias-canonicalize
                                       x idx w offset aliases)))))
      :hints ('(:expand ((:free (aliases) (lhrange-alias-canonicalize x idx w offset aliases))
                         (:free (x) (lhs-vars (list x)))
                         (lhs-vars nil))
                :in-theory (enable svar-boundedp))
              (and stable-under-simplificationp
                   '(:in-theory (enable lhatom-vars
                                        lhatom-bound-fix))))
      :flag lhrange-alias-canonicalize)))



(defines lhs-alias-canonicalize-replace
  (define lhs-alias-canonicalize-replace
    ((x lhs-p) (idx natp) (w natp) (offset natp) (aliases aliases-normorderedp))
    :guard (and (< idx (aliass-length aliases))
                (or (zp w) (lhs-vars-normorderedp idx offset x)))
    :verify-guards nil
    :measure (nat-list-measure (list idx w offset (+ 1 (len x))))
    :returns (mv (canon (and (lhs-p canon)
                             (implies (natp idx)
                                      (lhs-vars-normorderedp idx offset canon)))
                    :hints ('(:expand ((lhs-alias-canonicalize-replace x idx w offset aliases)
                                       (lhs-vars-normorderedp idx offset nil)))))
                 (aliases1 aliases-normorderedp))
    (b* (((mv first rest) (lhs-decomp x))
         ((unless (and first (posp w)))
          (b* ((aliases (aliases-bound-fix aliases)))
            (mv nil aliases)))
         (blockw (min w (lhrange->w first)))
         ((mv newfirst aliases)
          (lhrange-alias-canonicalize-replace first idx blockw offset aliases))
         ((mv newrest aliases)
          (lhs-alias-canonicalize-replace rest idx
                                          (- w blockw)
                                          (+ (lnfix offset) blockw)
                                          aliases)))
      (mv (lhs-concat blockw newfirst newrest)
          aliases)))
  (define lhrange-alias-canonicalize-replace ((x lhrange-p) (idx natp) (w posp) (offset natp)
                                              (aliases aliases-normorderedp))
    :guard (and (< idx (aliass-length aliases))
                (<= w (lhrange->w x))
                (lhatom-normorderedp idx offset (lhrange->atom x)))
    :measure (nat-list-measure (list idx (acl2::pos-fix w) offset 0))
    :returns (mv (canon (and (lhs-p canon)
                             (implies (natp idx)
                                      (lhs-vars-normorderedp idx offset canon)))
                    :hints ('(:expand ((lhrange-alias-canonicalize-replace x idx w offset aliases)
                                       (:free (offset) (lhs-vars-normorderedp idx offset nil))
                                       (:free (x) (lhs-vars-normorderedp idx offset (list x)))))))
                 (aliases1 aliases-normorderedp))
    (b* (((lhrange x) x)
         (x.atom (lhatom-bound-fix (lnfix idx) offset x.atom)))
      (lhatom-case x.atom
        :z (b* ((aliases (aliases-bound-fix aliases)))
             (mv nil aliases))
        :var (b* ((vidx (svar-index x.atom.name))
                  ((when (and (eql vidx (lnfix idx))
                              (eql x.atom.rsh (lnfix offset))))
                   (b* ((aliases (aliases-bound-fix aliases)))
                     (mv (list (lhrange w x.atom)) aliases)))
                  (w (mbe :logic (acl2::pos-fix w) :exec w))
                  (whole-lhs (getalias vidx aliases))
                  (leftpart (lhs-rsh x.atom.rsh whole-lhs))
                  ((mv canon aliases)
                   (lhs-alias-canonicalize-replace
                    leftpart vidx w x.atom.rsh aliases))
                  (leftpart2 (lhs-rsh (lnfix w) leftpart))
                  (whole-canon (lhs-concat x.atom.rsh whole-lhs
                                           (lhs-concat w canon leftpart2)))
                  (aliases (setalias vidx whole-canon aliases)))
               (mv canon aliases)))))
  ///
  (deffixequiv-mutual lhs-alias-canonicalize-replace
    :hints (("goal" :expand ((:free (idx offset w)
                              (lhs-alias-canonicalize-replace
                               x idx w offset aliases))
                             (:free (idx offset w)
                              (lhs-alias-canonicalize-replace
                               (lhs-fix x) idx w offset aliases))
                             (:free (idx offset w)
                              (lhrange-alias-canonicalize-replace
                               x idx w offset aliases))
                             (:free (idx offset w)
                              (lhrange-alias-canonicalize-replace
                               (lhrange-fix x) idx w offset aliases))
                             (lhs-alias-canonicalize-replace
                              x idx w offset (aliases-bound-fix aliases))))))

  (defthm-lhs-alias-canonicalize-replace-flag
    (defthm len-of-lhs-alias-canonicalize-replace
      (implies (< (nfix idx) (len aliases))
               (equal (len (mv-nth 1 (lhs-alias-canonicalize-replace
                                      x idx w offset aliases)))
                      (len aliases)))
      :hints ('(:expand (lhs-alias-canonicalize-replace x idx w offset aliases)))
      :flag lhs-alias-canonicalize-replace)
    (defthm len-of-lhrange-alias-canonicalize-replace
      (implies (< (nfix idx) (len aliases))
               (equal (len (mv-nth 1 (lhrange-alias-canonicalize-replace
                                      x idx w offset aliases)))
                      (len aliases)))
      :hints ('(:expand ((lhrange-alias-canonicalize-replace x idx w offset aliases))))
      :flag lhrange-alias-canonicalize-replace))

  (defthm-lhs-alias-canonicalize-replace-flag
    (defthm getalias-greater-of-lhs-alias-canonicalize-replace
      (implies (< (nfix idx) (nfix n))
               (equal (getalias n (mv-nth 1 (lhs-alias-canonicalize-replace
                                             x idx w offset aliases)))
                      (getalias n aliases)))
      :hints ('(:expand (lhs-alias-canonicalize-replace x idx w offset aliases)))
      :flag lhs-alias-canonicalize-replace)
    (defthm getalias-greater-of-lhrange-alias-canonicalize-replace
      (implies (< (nfix idx) (nfix n))
               (equal (getalias n (mv-nth 1 (lhrange-alias-canonicalize-replace
                                             x idx w offset aliases)))
                      (getalias n aliases)))
      :hints ('(:expand ((lhrange-alias-canonicalize-replace x idx w offset aliases))))
      :flag lhrange-alias-canonicalize-replace))

  ;; (defthm-lhs-alias-canonicalize-replace-flag
  ;;   (defthm lhs-alias-canonicalize-replace-same-as-canonicalize
  ;;     (equal (mv-nth 0 (lhs-alias-canonicalize-replace
  ;;                       x idx w offset aliases))
  ;;            (lhs-alias-canonicalize x idx w offset aliases))
  ;;     :hints ('(:expand ((lhs-alias-canonicalize-replace x idx w offset aliases)
  ;;                        (lhs-alias-canonicalize x idx w offset aliases)
  ;;                        (:free (x offset)
  ;;                         (lhs-alias-canonicalize x idx 0 offset aliases)))))
  ;;     :flag lhs-alias-canonicalize-replace)
  ;;   (defthm lhrange-alias-canonicalize-replace-same-as-canonicalize
  ;;     (equal (mv-nth 0 (lhrange-alias-canonicalize-replace
  ;;                       x idx w offset aliases))
  ;;            (lhrange-alias-canonicalize x idx w offset aliases))
  ;;     :hints ('(:expand ((lhrange-alias-canonicalize-replace x idx w offset aliases)
  ;;                        (lhrange-alias-canonicalize x idx w offset aliases))))
  ;;     :flag lhrange-alias-canonicalize-replace))


  (verify-guards lhs-alias-canonicalize-replace
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance lhs-vars-normorderedp
                          (bound idx)
                          (x (lhs-norm x))))
                   :in-theory (disable lhs-vars-normorderedp-implies-rest)))))

  (local (defthm-lhs-alias-canonicalize-replace-flag
           (defthm lhs-alias-canonicalize-replace-of-lhs-norm
             (equal (lhs-alias-canonicalize-replace (lhs-norm x) idx w offset aliases)
                    (lhs-alias-canonicalize-replace x idx w offset aliases))
             :hints ('(:expand ((lhs-alias-canonicalize-replace x idx w offset aliases)
                                (lhs-alias-canonicalize-replace (lhs-norm x) idx w offset aliases))))
             :flag lhs-alias-canonicalize-replace)
           :skip-others t))

  (fty::deffixcong lhs-norm-equiv equal (lhs-alias-canonicalize-replace x idx w offset aliases) x
    :hints (("goal" :expand ((lhs-alias-canonicalize-replace x idx w offset aliases)
                             (lhs-alias-canonicalize-replace (lhs-norm x) idx w offset aliases)))))

  (defthm-lhs-alias-canonicalize-replace-flag
    (defthm lhs-boundedp-of-lhs-alias-canonicalize-replace
      (implies (and (< (nfix idx) (len aliases))
                    (not (svar-boundedp v (len aliases))))
               (not (member v (lhs-vars (mv-nth 0 (lhs-alias-canonicalize-replace x idx w offset aliases))))))
      :hints ('(:expand ((:free (aliases) (lhs-alias-canonicalize-replace x idx w offset aliases))
                         (lhs-vars nil))))
      :flag lhs-alias-canonicalize-replace)
    (defthm lhs-boundedp-of-lhrange-alias-canonicalize-replace
      (implies (and (< (nfix idx) (len aliases))
                    (not (svar-boundedp v (len aliases))))
               (not (member v (lhs-vars (mv-nth 0 (lhrange-alias-canonicalize-replace
                                                   x idx w offset aliases))))))
      :hints ('(:expand ((:free (aliases) (lhrange-alias-canonicalize-replace x idx w offset aliases))
                         (:free (x) (lhs-vars (list x)))
                         (lhs-vars nil))
                :in-theory (enable svar-boundedp))
              (and stable-under-simplificationp
                   '(:in-theory (enable lhatom-vars
                                        lhatom-bound-fix))))
      :flag lhrange-alias-canonicalize-replace)))




(define lhs-replace-range ((start natp) (w natp) (repl lhs-p) (x lhs-p))
  :returns (newx lhs-p)
  (lhs-concat start x
              (lhs-concat w repl
                          (lhs-rsh (+ (lnfix start) (lnfix w))
                                   x)))
  ///
  (deffixequiv lhs-replace-range)

  (defthm lhs-vars-normorderedp-of-lhs-replace-range
    (implies (and (lhs-vars-normorderedp n m x)
                  (lhs-vars-normorderedp n (+ (nfix m) (nfix start)) repl))
             (lhs-vars-normorderedp n m (lhs-replace-range start w repl x)))))


;; We're walking along x and y from bit offset 0 to the end.  Offset is the
;; total offset.  The range borders may not be at the same places; for now we
;; just recons a new first range on whichever has the larger one.






(with-output :off (prove)
  (define lhs-pairs-set-aliases ((x lhs-p) (y lhs-p) ;; (offset natp)
                                 (aliases aliases-normorderedp))
    :guard (and ;; (lhs-vars-normorderedp (1- (aliass-length aliases)) offset x)
                ;; (lhs-vars-normorderedp (1- (aliass-length aliases)) offset y)
            (svarlist-boundedp (lhs-vars x) (aliass-length aliases))
            (svarlist-boundedp (lhs-vars y) (aliass-length aliases))
                )
    :measure (+ (len x) (len y))
    :returns (aliases1 aliases-normorderedp
                       :hints (("goal" :induct (lhs-pairs-set-aliases
                                                x y aliases)
                                :expand ((lhs-pairs-set-aliases
                                          x y aliases))
                                :in-theory (disable (:d lhs-pairs-set-aliases)))))
    :verify-guards nil
    :ignore-ok t
    :irrelevant-formals-ok t
    :prepwork ((local (in-theory (disable lhatom-normorderedp-implies-index
                                          member-equal subsetp-equal
                                          lhs-norm-when-lhs-normp
                                          lhs-norm-when-not-consp
                                          rationalp-implies-acl2-numberp
                                          not default-cdr
                                          posp-of-lhrange->w
                                          (:t lhrange->w)
                                          (:t lhatom-kind)
                                          (:t natp-of-lhatom-var->rsh)
                                          (:t lhrange->atom)
                                          (:t lhs-norm)
                                          (:t svar-index)
                                          ; (:t lhatom-var->rsh)
                                          (:t svarlist-boundedp)
                                          default-car) )))
    ;; :guard-hints (("goal" :use ((:instance lhs-vars-normorderedp
    ;;                              (bound (1- (len aliases)))
    ;;                              (x (lhs-norm x)))
    ;;                             (:instance lhs-vars-normorderedp
    ;;                              (bound (1- (len aliases)))
    ;;                              (x (lhs-norm y))))
    ;;                :expand ((:free (bound offset a b)
    ;;                          (lhs-vars-normorderedp bound offset (cons a b))))
    ;;                :do-not-induct t
    ;;                :in-theory (disable lhs-vars-normorderedp)))
    ;; :guard-debug t
    (b* (((mv xf xrest) (lhs-decomp x))
         ((mv yf yrest) (lhs-decomp y))
         ((when (or (not xf) (not yf)))
          (aliases-bound-fix aliases))
         ((lhrange xf) xf)
         ((lhrange yf) yf)
         ;; (xf.atom (lhatom-bound-fix (1- (aliass-length aliases)) offset xf.atom))
         ;; (yf.atom (lhatom-bound-fix (1- (aliass-length aliases)) offset yf.atom))
         ;; (offset (lnfix offset))
         (xkind (lhatom-kind xf.atom))
         (ykind (lhatom-kind yf.atom))
         ((mv blkw nextx nexty)
          (cond ((< xf.w yf.w) (mv xf.w
                                   xrest
                                   (lhs-rsh xf.w y)))
                ((< yf.w xf.w) (mv yf.w
                                   (lhs-rsh yf.w x)
                                   yrest))
                (t (mv xf.w xrest yrest))))
         ((unless (and (eql (lhatom-kind xf.atom) :var)
                       (eql (lhatom-kind yf.atom) :var)
                       (not (equal xf.atom yf.atom))))
          ;; skip
          (lhs-pairs-set-aliases nextx nexty ;; (+ blkw offset)
                                 aliases))
         ((lhatom-var xf.atom) xf.atom)
         ((lhatom-var yf.atom) yf.atom)
         (xidx (svar-index xf.atom.name))
         (yidx (svar-index yf.atom.name))
         ((mv less-idx less-offset gr-idx gr-offset)
          (cond ((< xidx yidx)                (mv xidx xf.atom.rsh yidx yf.atom.rsh))
                ((< yidx xidx)                (mv yidx yf.atom.rsh xidx xf.atom.rsh))
                ((< xf.atom.rsh yf.atom.rsh)  (mv xidx xf.atom.rsh yidx yf.atom.rsh))
                (t                            (mv yidx yf.atom.rsh xidx xf.atom.rsh))))
         (greater-full (getalias gr-idx aliases))
         (less-full (getalias less-idx aliases))
         (less-range (lhs-rsh less-offset less-full))
         (greater-new (lhs-replace-range gr-offset blkw less-range greater-full))
         (aliases (setalias gr-idx greater-new aliases)))
      (lhs-pairs-set-aliases nextx nexty ;; (+ blkw offset)
                             aliases))

    ///

    (local (defthm lhs-vars-normorderedp-of-getalias-forward
             (implies (natp idx)
                      (lhs-vars-normorderedp idx 0 (getalias idx aliases)))
             :rule-classes
             ((:forward-chaining :trigger-terms ((getalias idx aliases))))))

    (verify-guards lhs-pairs-set-aliases
      :hints (("goal" :expand ((:free (idx offset a b)
                                (lhs-vars-normorderedp idx offset (cons a b))))
               :in-theory (e/d (lhatom-normorderedp)
                               ((force) len not
                                lhatom-normorderedp-implies-index
                                lhs-pairs-set-aliases)))
              (and stable-under-simplificationp
                   '(:expand ((lhs-vars x)
                              (lhs-vars y))
                     :in-theory (enable svar-boundedp lhatom-vars)))))

    (defthm len-of-lhs-pairs-set-aliases-bound
      (>= (len (lhs-pairs-set-aliases x y aliases))
          (len aliases))
      :hints (("goal" :induct (lhs-pairs-set-aliases x y aliases)
               :expand ((lhs-pairs-set-aliases x y aliases))
               :in-theory (disable (:d lhs-pairs-set-aliases))))
      :rule-classes :linear)


    (local (defthm svar-index-when-svar-boundedp
             (implies (svar-boundedp x bound)
                      (and (< (svar-index x) bound)
                           (< (nfix (svar-index x)) bound)))
             :hints(("Goal" :in-theory (enable svar-boundedp)))
             :rule-classes :linear))

    (defthm len-of-lhs-pairs-set-aliases
      (implies (and (svarlist-boundedp (lhs-vars x) (len aliases))
                    (svarlist-boundedp (lhs-vars y) (len aliases)))
               (equal (len (lhs-pairs-set-aliases x y aliases))
                      (len aliases)))
      :hints (("goal" :induct (lhs-pairs-set-aliases x y aliases)
               :in-theory (e/d (lhatom-vars acl2::mv-nth-cons-meta)
                               ((:d lhs-pairs-set-aliases)
                                lhatom-normorderedp-implies-index
                                lhs-norm-when-lhs-normp
                                member default-car subsetp
                                svarlist-boundedp-when-subsetp-equal
                                not acl2::mv-nth-of-cons)))
              '(:expand ((lhs-pairs-set-aliases x y aliases)))))

    (deffixequiv lhs-pairs-set-aliases
      :hints (("goal" :induct (lhs-pairs-set-aliases x y aliases)
               :expand ((lhs-pairs-set-aliases x y aliases)
                        (lhs-pairs-set-aliases (lhs-fix x) y aliases)
                        (lhs-pairs-set-aliases x (lhs-fix y) aliases)
                        (lhs-pairs-set-aliases x y aliases)
                        (lhs-pairs-set-aliases x y (aliases-bound-fix aliases)))
               :in-theory (disable (:d lhs-pairs-set-aliases)))))))


(local (in-theory (disable lhs-vars-when-consp)))

(define lhs-alias-canonicalize-top ((x lhs-p) (aliases aliases-normorderedp))
  :guard (svarlist-boundedp (lhs-vars x) (aliass-length aliases))
  :verify-guards nil
  :measure (len x)
  :returns (xx (and (lhs-p xx)
                    (implies (svarlist-boundedp (lhs-vars x) (len aliases))
                             (svarlist-boundedp (lhs-vars xx) (len aliases))))
               :hints (("goal" :induct t)
                       (and stable-under-simplificationp
                            '(:expand ((lhs-vars nil)
                                       (lhs-vars x))
                              :in-theory (e/d (svar-boundedp lhatom-vars)
                                              (lhs-vars-when-consp))))))
  (b* (((mv first rest) (lhs-decomp x))
       ((unless first) nil)
       ((lhrange first) first))
    (lhatom-case first.atom
      :z (lhs-cons first (lhs-alias-canonicalize-top rest aliases))
      :var (b* ((idx (svar-index first.atom.name)))
             (lhs-concat first.w
                         (lhs-alias-canonicalize
                          (lhs-rsh first.atom.rsh (getalias idx aliases))
                          idx first.w first.atom.rsh aliases)
                         (lhs-alias-canonicalize-top rest aliases)))))
  ///
  (verify-guards lhs-alias-canonicalize-top
    :hints ((and stable-under-simplificationp
                 '(:expand ((lhs-vars x))
                   :in-theory (enable svar-boundedp lhatom-vars)))))

  (deffixequiv lhs-alias-canonicalize-top))

(define lhs-alias-canonicalize-replace-top ((x lhs-p) (aliases aliases-normorderedp))
  :guard (svarlist-boundedp (lhs-vars x) (aliass-length aliases))
  :verify-guards nil
  :measure (len x)
  :returns (mv  (xx (and (lhs-p xx)
                         (implies (svarlist-boundedp (lhs-vars x) (len aliases))
                                  (svarlist-boundedp (lhs-vars xx) (len aliases))))
                    :hints (("goal" :induct t)
                            (and stable-under-simplificationp
                                 '(:expand ((lhs-vars nil)
                                            (lhs-vars x))
                                   :in-theory (enable svar-boundedp lhatom-vars)))))
                (aliases1 (and (aliases-normorderedp aliases1)
                               (implies (svarlist-boundedp (lhs-vars x) (len aliases))
                                        (equal (len aliases1)
                                               (len aliases))))

                          :hints (("goal" :induct t)
                                  (and stable-under-simplificationp
                                       '(:expand ((lhs-vars nil)
                                                  (lhs-vars x))
                                         :in-theory (enable svar-boundedp lhatom-vars))))))
  (b* (((mv first rest) (lhs-decomp x))
       ((unless first) (let ((aliases (aliases-bound-fix aliases)))
                         (mv nil aliases)))
       ((lhrange first) first))
    (lhatom-case first.atom
      :z (b* (((mv restx aliases) (lhs-alias-canonicalize-replace-top rest aliases)))
           (mv (lhs-cons first restx) aliases))
      :var (b* ((idx (svar-index first.atom.name))
                (alias (getalias idx aliases))
                ;; (- (cw "idx: ~x0, val ~x1~%" idx alias))
                ((mv firstx aliases)
                 (lhs-alias-canonicalize-replace
                  (lhs-rsh first.atom.rsh alias)
                  idx first.w first.atom.rsh aliases))
                ((mv restx aliases)
                 (lhs-alias-canonicalize-replace-top rest aliases)))
             (mv (lhs-concat first.w firstx restx)
                 aliases))))
  ///
  (verify-guards lhs-alias-canonicalize-replace-top
    :hints ((and stable-under-simplificationp
                 '(:expand ((lhs-vars x))
                   :in-theory (enable svar-boundedp lhatom-vars)))))

  (defthm len-aliases-of-lhs-alias-canonicalize-replace-top
    (implies (svarlist-boundedp (lhs-vars x) (len aliases))
             (equal (len (mv-nth 1 (lhs-alias-canonicalize-replace-top x aliases)))
                    (len aliases)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((lhs-vars x))
                   :in-theory (enable svar-boundedp)))))

  (deffixequiv lhs-alias-canonicalize-replace-top))


(define lhs-alias-norm ((x lhs-p) aliases)
  :guard (svarlist-boundedp (lhs-vars x) (aliass-length aliases))
  :verify-guards nil
  :measure (len x)
  :returns (xx lhs-p)
  (b* (((mv first rest) (lhs-decomp x))
       ((unless first) nil)
       ((lhrange first) first))
    (lhatom-case first.atom
      :z (lhs-cons first (lhs-alias-norm rest aliases))
      :var (b* ((idx (svar-index first.atom.name)))
             (lhs-concat first.w
                         (lhs-rsh first.atom.rsh (get-alias idx aliases))
                         (lhs-alias-norm rest aliases)))))
  ///
  (verify-guards lhs-alias-norm
    :hints ((and stable-under-simplificationp
                 '(:expand ((lhs-vars x))
                   :in-theory (enable svar-boundedp lhatom-vars)))))

  (deffixequiv lhs-alias-norm)

  (defthm vars-of-lhs-alias-norm
    (implies (not (member v (aliases-vars aliases)))
             (not (member v (lhs-vars (lhs-alias-norm x aliases)))))
    :hints(("Goal" :in-theory (enable lhatom-vars)))))




(define aliases-add-pair ((x lhs-p) (y lhs-p) (aliases aliases-normorderedp))
  :guard (and (svarlist-boundedp (lhs-vars x) (aliass-length aliases))
              (svarlist-boundedp (lhs-vars y) (aliass-length aliases)))
  :returns (aliases1 aliases-normorderedp)
  (b* (((when (zp (aliass-length aliases)))
        (aliases-bound-fix aliases))
       (xcanon (lhs-alias-canonicalize-top x aliases))
       (ycanon (lhs-alias-canonicalize-top y aliases))
       (aliases (lhs-pairs-set-aliases xcanon ycanon aliases))
       ((mv & aliases) (lhs-alias-canonicalize-replace-top x aliases))
       ((mv & aliases) (lhs-alias-canonicalize-replace-top y aliases)))
    aliases)
  ///
  (deffixequiv aliases-add-pair)

  (defthm len-of-aliases-add-pair
    (implies (and (svarlist-boundedp (lhs-vars x) (len aliases))
                  (svarlist-boundedp (lhs-vars y) (len aliases)))
             (equal (len (aliases-add-pair x y aliases))
                    (len aliases)))))

(define aliases-finish-canonicalize ((n natp) (aliases aliases-normorderedp))
  :guard (<= n (aliass-length aliases))
  :returns (aliases1 aliases-normorderedp)
  :measure (nfix (- (aliass-length aliases) (nfix n)))
  (b* (((when (mbe :logic (zp (- (aliass-length aliases) (nfix n)))
                   :exec (eql (aliass-length aliases) n)))
        (aliases-bound-fix aliases))
       (lhs (getalias n aliases))
       (canon (lhs-alias-canonicalize lhs n (lhs-width lhs) 0 aliases))
       (aliases (setalias n canon aliases)))
    (aliases-finish-canonicalize (1+ (lnfix n)) aliases))
  ///
  (deffixequiv aliases-finish-canonicalize)

  (defthm len-of-aliases-finish-canonicalize
    (equal (len (aliases-finish-canonicalize n aliases))
           (len aliases))))

(define aliases-empty (aliases)
  :enabled t
  (mbe :logic (non-exec nil)
       :exec (resize-aliass 0 aliases)))

;; (define lhspairs-normorderedp ((len natp) (x lhspairs-p))
;;   (if (atom x)
;;       t
;;     (if (mbt (consp (car x)))
;;         (b* ((len (lnfix len)))
;;           (and (lhs-vars-normorderedp (1- len) 0 (caar x))
;;                (lhs-vars-normorderedp (1- len) 0 (cdar x))
;;                (lhspairs-normorderedp len (cdr x))))
;;       (lhspairs-normorderedp len (cdr x))))
;;   ///
;;   (deffixequiv lhspairs-normorderedp
;;     :hints (("goal" :induct (lhspairs-normorderedp len x)
;;              :expand (lhspairs-fix x)))))

(define aliases-put-pairs ((pairs lhspairs-p) (aliases aliases-normorderedp))
  :guard (svarlist-boundedp (lhspairs-vars pairs) (aliass-length aliases))
  :returns (aliases1 aliases-normorderedp)
  :guard-hints (("goal" :expand ((lhspairs-vars pairs))))
  :measure (len (lhspairs-fix pairs))
  (b* ((pairs (lhspairs-fix pairs))
       ((when (atom pairs)) (aliases-bound-fix aliases))
       ((unless (mbt (consp (car pairs))))
        (aliases-put-pairs (cdr pairs) aliases))
       ((cons x y) (car pairs))
       (aliases (aliases-add-pair x y aliases)))
    (aliases-put-pairs (cdr pairs) aliases))
  ///
  (deffixequiv aliases-put-pairs
    :hints(("Goal" :in-theory (enable lhspairs-fix))))

  (defthm len-of-aliases-put-pairs
    (implies (svarlist-boundedp (lhspairs-vars pairs) (len aliases))
             (equal (len (aliases-put-pairs pairs aliases))
                    (len aliases)))
    :hints(("Goal" :induct t :in-theory (enable lhspairs-vars)))))

(define canonicalize-alias-pairs ((pairs lhspairs-p) (aliases aliases-normorderedp))
  :guard (svarlist-boundedp (lhspairs-vars pairs) (aliass-length aliases))
  :returns (aliases aliases-normorderedp)
  (b* ((aliases (aliases-put-pairs pairs aliases)))
    (aliases-finish-canonicalize 0 aliases))
  ///
  (deffixequiv canonicalize-alias-pairs)

  (defthm len-of-canonicalize-alias-pairs
    (implies (svarlist-boundedp (lhspairs-vars pairs) (len aliases))
             (equal (len (canonicalize-alias-pairs pairs aliases))
                    (len aliases)))))








(defines svex-subst-from-svexarr
  :verify-guards nil
  (define svex-subst-from-svexarr ((x svex-p) svexarr)
    :guard (svarlist-boundedp (svex-vars x) (svexs-length svexarr))
    :returns (xx svex-p)
    :measure (svex-count x)
    (svex-case x
      :var (svex-add-delay-top (get-svex (svar-index x.name) svexarr)
                               (svar->delay x.name))
      :quote (svex-fix x)
      :call (svex-call* x.fn (svexlist-subst-from-svexarr x.args svexarr))))

  (define svexlist-subst-from-svexarr ((x svexlist-p) svexarr)
    :guard (svarlist-boundedp (svexlist-vars x) (svexs-length svexarr))
    :returns (xx svexlist-p)
    :measure (svexlist-count x)
    (if (atom x)
        nil
      (cons (svex-subst-from-svexarr (car x) svexarr)
            (svexlist-subst-from-svexarr (cdr x) svexarr))))
  ///
  (verify-guards svex-subst-from-svexarr
    :hints ((and stable-under-simplificationp
                 '(:expand ((svex-vars x)
                            (svexlist-vars x))
                   :in-theory (enable svar-boundedp)))))

  (defthm-svex-subst-from-svexarr-flag
    (defthm svarlist-addr-p-of-svex-subst-from-svexarr
      (implies (svarlist-addr-p (svexarr-vars svexarr))
               (svarlist-addr-p (svex-vars (svex-subst-from-svexarr x svexarr))))
      :flag svex-subst-from-svexarr)
    (defthm svarlist-addr-p-of-svexlist-subst-from-svexarr
      (implies (svarlist-addr-p (svexarr-vars svexarr))
               (svarlist-addr-p (svexlist-vars (svexlist-subst-from-svexarr x svexarr))))
      :flag svexlist-subst-from-svexarr))

  ;; BOZO memoizing this likely makes all svexarr operations slow
  (define svex-subst-from-svexarr-memo-ok ((x svex-p) svexarr)
    :guard (svarlist-boundedp (svex-vars x) (svexs-length svexarr))
    :inline t
    :ignore-ok t
    (eq (svex-kind x) :call))

  (memoize 'svex-subst-from-svexarr :condition-fn 'svex-subst-from-svexarr-memo-ok$inline))

(define assigns-subst-nrev ((x assigns-p) aliases svexarr nrev)
  :guard (and (svarlist-boundedp (assigns-vars x) (aliass-length aliases))
              (svarlist-boundedp (assigns-vars x) (svexs-length svexarr)))
  :guard-hints (("goal" :expand ((assigns-vars x))))
  :measure (len (assigns-fix x))
  (b* ((x (assigns-fix x))
       ((when (atom x)) (acl2::nrev-fix nrev))
       ((cons lhs (driver rhs)) (car x))
       (lhs (lhs-alias-norm lhs aliases))
       (val (svex-subst-from-svexarr rhs.value svexarr))
       (nrev (acl2::nrev-push (cons lhs (change-driver rhs :value val)) nrev)))
    (assigns-subst-nrev (cdr x) aliases svexarr nrev)))

(define assigns-subst ((x assigns-p) aliases svexarr)
  :guard (and (svarlist-boundedp (assigns-vars x) (aliass-length aliases))
              (svarlist-boundedp (assigns-vars x) (svexs-length svexarr)))
  :returns (xx assigns-p)
  :measure (len (assigns-fix x))
  :verify-guards nil
  (mbe :logic (b* ((x (assigns-fix x))
                   ((when (atom x)) nil)
                   ((cons lhs (driver rhs)) (car x))
                   (lhs (lhs-alias-norm lhs aliases))
                   (val (svex-subst-from-svexarr rhs.value svexarr)))
                (cons (cons lhs (change-driver rhs :value val))
                      (assigns-subst (cdr x) aliases svexarr)))
       :exec (if (atom x)
                 nil
               (with-local-stobj nrev
                 (mv-let (ans nrev)
                   (b* ((nrev (assigns-subst-nrev x aliases svexarr nrev))
                        ((mv ans nrev) (acl2::nrev-finish nrev)))
                     (mv ans nrev))
                   ans))))
  ///
  (local (defthm assigns-subst-nrev-elim
           (equal (assigns-subst-nrev x aliases svexarr nrev)
                  (append nrev (assigns-subst x aliases svexarr)))
           :hints(("Goal" :in-theory (enable assigns-subst-nrev acl2::rcons)))))

  (verify-guards assigns-subst :hints (("goal" :expand ((assigns-vars x)))))

  (deffixequiv assigns-subst)

  (defthm svarlist-addr-p-of-assigns-subst
    (implies (and (svarlist-addr-p (svexarr-vars svexarr))
                  (svarlist-addr-p (aliases-vars aliases)))
             (svarlist-addr-p (assigns-vars (assigns-subst x aliases svexarr))))
    :hints(("Goal" :in-theory (enable assigns-vars)))))


(define constraintlist-subst-from-svexarr-nrev ((x constraintlist-p) aliases svexarr nrev)
  :guard (and (svarlist-boundedp (constraintlist-vars x) (aliass-length aliases))
              (svarlist-boundedp (constraintlist-vars x) (svexs-length svexarr)))
  :guard-hints (("goal" :expand ((constraintlist-vars x))))
  (b* (((when (atom x)) (acl2::nrev-fix nrev))
       ((constraint x1) (car x))
       (cond (svex-subst-from-svexarr x1.cond svexarr))
       (nrev (acl2::nrev-push (change-constraint x1 :cond cond) nrev)))
    (constraintlist-subst-from-svexarr-nrev (cdr x) aliases svexarr nrev)))

(define constraintlist-subst-from-svexarr ((x constraintlist-p) aliases svexarr)
  :guard (and (svarlist-boundedp (constraintlist-vars x) (aliass-length aliases))
              (svarlist-boundedp (constraintlist-vars x) (svexs-length svexarr)))
  :returns (xx constraintlist-p)
  :verify-guards nil
  (mbe :logic (b* (((when (atom x)) nil)
                   ((constraint x1) (car x))
                   (cond (svex-subst-from-svexarr x1.cond svexarr)))
                (cons (change-constraint x1 :cond cond)
                      (constraintlist-subst-from-svexarr (cdr x) aliases svexarr)))
       :exec (if (atom x)
                 nil
               (with-local-stobj nrev
                 (mv-let (ans nrev)
                   (b* ((nrev (constraintlist-subst-from-svexarr-nrev x aliases svexarr nrev))
                        ((mv ans nrev) (acl2::nrev-finish nrev)))
                     (mv ans nrev))
                   ans))))
  ///
  (local (defthm constraintlist-subst-from-svexarr-nrev-elim
           (equal (constraintlist-subst-from-svexarr-nrev x aliases svexarr nrev)
                  (append nrev (constraintlist-subst-from-svexarr x aliases svexarr)))
           :hints(("Goal" :in-theory (enable constraintlist-subst-from-svexarr-nrev acl2::rcons)))))

  (verify-guards constraintlist-subst-from-svexarr :hints (("goal" :expand ((constraintlist-vars x)))))

  (deffixequiv constraintlist-subst-from-svexarr)

  (local (in-theory (disable svarlist-addr-p-by-badguy)))

  (defthm svarlist-addr-p-of-constraintlist-subst-from-svexarr
    (implies (and (svarlist-addr-p (svexarr-vars svexarr))
                  (svarlist-addr-p (aliases-vars aliases)))
             (svarlist-addr-p (constraintlist-vars (constraintlist-subst-from-svexarr x aliases svexarr))))
    :hints(("Goal" :in-theory (enable constraintlist-vars)))))





#||















(define varbit-alias-canonicalize ((idx natp)
                                   (varid natp)
                                   (aliases aliases-normorderedp))
  :measure (two-nats-measure varid idx)
  :guard (< varid (aliass-length aliases))
  :returns (xx lhbit-p)
  (b* ((bit (lhs-bitproj idx (get-alias varid aliases)))
       (idx (lnfix idx)) (varid (lnfix varid)))
    (lhbit-case bit
      :z bit
      :var (b* ((bitvarid (svar-index bit.name))
                ((unless (mbt (and bitvarid
                                   (or (< bitvarid varid)
                                       (and (eql bitvarid varid)
                                            (< bit.idx idx))))))
                 bit))
             (varbit-alias-canonicalize bit.idx bitvarid aliases))))
  ///
  (deffixequiv varbit-alias-canonicalize
    :hints (("goal" :expand ((varbit-alias-canonicalize idx varid aliases)
                             (varbit-alias-canonicalize (nfix idx) varid aliases)
                             (varbit-alias-canonicalize idx (nfix varid) aliases))))))

(define lhbit-alias-canonicalize ((x lhbit-p) aliases)
  :returns (xx lhbit-p)
  (lhbit-case x
    :z (lhbit-z)
    :var (b* ((varid (svar-index x.name))
              ((unless (and varid (< varid (aliass-length aliases))))
               (lhbit-fix x)))
           (varbit-alias-canonicalize x.idx varid aliases)))
  ///
  (deffixequiv lhbit-alias-canonicalize))

;; (define maybe-nat-fix ((x maybe-natp))
;;   :returns (xx maybe-natp)
;;   (mbe :logic (and x (nfix x))
;;        :exec x)
;;   ///
;;   (defthm maybe-nat-fix-when-maybe-natp
;;     (implies (maybe-natp x)
;;              (equal (maybe-nat-fix x) X)))
;;   (deffixtype maybe-nat :pred maybe-natp :fix maybe-nat-fix
;;     :equiv maybe-nat-equiv :define t :forward t)
;;   (defthm maybe-nat-fix-undef-nat-equiv
;;     (implies x
;;              (nat-equiv (maybe-nat-fix x)
;;                         x)))
;;   (defthm maybe-nat-fix-under-iff
;;     (iff (maybe-nat-fix x) x)))







(defines lhs-alias-canonicalize-ind
  (define lhs-alias-canonicalize-ind ((x lhs-p) (idx natp) (w natp) (offset natp)
                                      (bitidx natp)
                                      aliases)
    :guard (< idx (aliass-length aliases))
    :verify-guards nil
    :measure (nat-list-measure (list idx w offset (+ 1 (len x))))
    (if (or (atom x)
            (zp w))
        nil
      (let ((blockw (min w (lhrange->w (car x)))))
        (if (< (nfix bitidx) (lhrange->w (car x)))
            (lhrange-alias-canonicalize-ind (car x) idx blockw offset bitidx aliases)
          (lhs-alias-canonicalize-ind (cdr x) idx
                                      (- w blockw)
                                      (+ (lnfix offset) blockw)
                                      (- (nfix bitidx) blockw)
                                      aliases)))))
  (define lhrange-alias-canonicalize-ind ((x lhrange-p) (idx natp) (w natp) (offset natp)
                                          (bitidx natp)
                                          aliases)
    :guard (< idx (aliass-length aliases))
    :measure (nat-list-measure (list idx w offset 0))
    (b* (((lhrange x) x))
      (lhatom-case x.atom
        :z (list (lhrange-fix x))
        :var (let ((vidx (svar-index x.atom.name)))
               (if (and vidx
                        (or (< vidx (lnfix idx))
                            (and (eql vidx (lnfix idx)) (< x.atom.rsh (lnfix offset)))))
                   (lhs-alias-canonicalize-ind
                    (lhs-rsh
                     x.atom.rsh
                     (get-alias vidx aliases))
                    vidx (min (lnfix w) x.w) x.atom.rsh bitidx aliases)
                 (list (lhrange-fix x)))))))
  ///

  (defthm-lhs-alias-canonicalize-ind-flag
    (defthm lhs-alias-canonicalize-bitproj-correct
      (implies (and (< (nfix bitidx) (nfix w))
                    (equal (lhs-bitproj bitidx x)
                           (lhs-bitproj (+ (nfix bitidx)
                                           (nfix offset))
                                        (get-alias idx aliases))))
               (equal (lhs-bitproj bitidx (lhs-alias-canonicalize
                                           x idx w offset aliases))
                      (lhbit-alias-canonicalize
                       (lhs-bitproj bitidx x) aliases)))
      :hints ('(:expand ((lhs-alias-canonicalize
                          x idx w offset aliases))))
      :flag lhs-alias-canonicalize-ind)
    (defthm lhrange-alias-canonicalize-ind
      (implies (and (< (nfix bitidx) (nfix w))
                    (equal (lhrange-bitproj bitidx x)
                           (lhs-bitproj (+ (nfix bitidx)
                                           (nfix offset))
                                        (get-alias idx aliases))))
               (equal (lhs-bitproj bitidx (lhrange-alias-canonicalize
                                           x idx w offset aliases))
                      (lhbit-alias-canonicalize
                       (lhrange-bitproj bitidx x) aliases)))
      :hints ('(:expand ((lhrange-alias-canonicalize
                          x idx w offset aliases)
                         (:free (a b)
                          (lhs-bitproj bitidx (cons a b)))
                         (:free (idx) (lhs-bitproj idx nil))
                         (varbit-alias-canonicalize
                          (+ (NFIX BITIDX)
                             (LHATOM-VAR->RSH (LHRANGE->ATOM X)))
                          (svar-index (lhatom-var->name (lhrange->atom x)))
                          aliases))
                :in-theory (enable lhbit-alias-canonicalize
                                   lhrange-bitproj
                                   lhatom-bitproj)
                :do-not-induct t))
      :flag lhrange-alias-canonicalize-ind)
    :hints(("Goal" :in-theory (enable lhbit-alias-canonicalize)))))


(define lhs-alias-canonicalize-top ((idx natp) aliases)
  :returns (canon lhs-p)
  :guard (< idx (aliass-length aliases))
  (let ((lhs (get-alias idx aliases)))
    (lhs-alias-canonicalize lhs idx (lhs-width lhs) 0 aliases))
  ///
  (deffixequiv lhs-alias-canonicalize-top))

(resize-aliass 10 aliases)

(set-alias 0 (list (lhrange 5 0 (lhatom-z))
                   (lhrange 7 5 (lhatom-var '(:var 0)))
                   (lhrange 13 3 (lhatom-var '(:var 0))))
           aliases)

(lhrange-alias-canonicalize (lhrange 25 0 (lhatom-var '(:var 0))) 1 25 0 aliases)

||#





(define collect-aliases ((n natp) aliases)
  ;; for debugging, mostly
  :guard (<= n (aliass-length aliases))
  :measure (nfix (- (aliass-length aliases) (nfix n)))
  (b* (((when (mbe :logic (zp (- (aliass-length aliases) (nfix n)))
                   :exec (eql n (aliass-length aliases))))
        nil))
    (cons (get-alias n aliases)
          (collect-aliases (1+ (lnfix n)) aliases))))
