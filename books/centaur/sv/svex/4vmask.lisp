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
(include-book "svex")
(include-book "centaur/bitops/sparseint" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/acl2-count" :dir :system))
(local (acl2::ruletable-delete-tags! acl2::listp-rules (:osets :duplicated-members)))


;; [BOZO] Rescue this comment, but I think it goes in the
;; svexlist-compose-to-fix stuff rather than in the 4vmask stuff.


;; Motivating example 1:
;; Suppose we have something like
;; wire [7:0] a;
;; wire [7:0] b;
;; assign a =  b | { a[6:0], 1'b0 };
;; This looks like a loop, but is actually legitimate at the bit level --
;; each a[i] equals | b[i:0].

;; How would we process this to a fixpoint?
;; If we expand a as-is, we get something like
;; assign a = b | { ( b | { a[6:0], 1'b0 } )[6:0], 1'b0 }
;; and we could just keep doing this forever.  What we'd like is for one such
;; expansion to give us something that's now in terms of a[5:0], the next in
;; terms of a[4:0], until we eliminate a from the formula altogether.

;; First, it helps if we explicitly put a size on our original formula.
;; Let's also write a[6:0] as trunc(7, a).
;; assign a = trunc(8, b | { trunc(7, a), 1'b0 });
;; We can push the trunc inside the OR and the concatenation:
;; assign a = trunc(8, b) | { trunc(7, trunc(7, a)), 1'b0 }
;; and simplify the trunc-of-trunc:
;; assign a = trunc(8, b) | { trunc(7, a), 1'b0 }
;; Now if we expand a and again push the trunc(7, ) inside, we get
;; assign a = trunc(8, b) | { trunc(7, trunc(8, b) | { trunc(7, a), 1'b0 } ), 1'b0 }
;; assign a = trunc(8, b) | { trunc(7, trunc(8, b)) | { trunc(6, trunc(7, a)), 1'b0 } ), 1'b0 }
;; simplify the trunc-of-trunc:
;; assign a = trunc(8, b) | { trunc(7, b) | { trunc(6, a), 1'b0 } ), 1'b0 }
;; and expanding more:
;; assign a = trunc(8, b) |
;;            { trunc(7, b) |
;;              { trunc(6, b) |
;;                { trunc(5, b) |
;;                  {trunc(4, b) |
;;                    { trunc(3, b) |
;;                      { trunc(2, b) |
;;                        { trunc(1, b) | 1'b0
;;                         , 1'b0 }
;;                       , 1'b0 }
;;                     , 1'b0 }
;;                   , 1'b0 }
;;                 , 1'b0 }
;;               , 1'b0 }
;;             , 1'b0 }

;; Another way of accomplishing this might be to just keep track of a care
;; mask.  Then, we can use a stylized kind of rule to say how we can update
;; that context as we go down into arguments of functions, e.g.:




(defxdoc 4vmask
  :parents (expressions)
  :short "Bitmasks indicating the relevant bits of SVEX expressions."

  :long "<p>A <b>4vmask</b> is a data structure that records which bits of an
expression we care about.</p>

<p>We represent 4vmasks as ordinary integers, which we treat as bit masks where
1s encode the relevant bit positions and 0s encode the irrelevant positions.
However, rather than directly using the @(see integerp) type, we treat 4vmasks
as a new, custom type, with its own recognizer, fixing function, etc.  This
gives us a semantically nicer fixing behavior where the default mask is -1,
i.e., by default all bits are relevant.</p>

<p>4vmasks are intended to support @(see rewriting) and other applications,
e.g., composing update functions to reach a fixpoint.  In these contexts,
knowing that certain bits of an @(see svex) expression are irrelevant can allow
for additional simplifications.  For instance, in an expression like:</p>

@({
     (zerox 4 (bitand <a> <b>))
})

<p>we can see that only the bottom four bits of @('<a>') and @('<b>') matter,
because the zero extension will discard anything above four bits.  By taking
advantage of this information, we may be able to simplify @('<a>') or @('<b>')
in ways that are would otherwise not be sound.  For instance, if @('<a>') is an
expression such as:</p>

@({
     (concat 4 <low> <high>)
})

<p>Then we can simply rewrite it to @('<low>') and get rid of @('<high>')
altogether.  Typically we make these sorts of inferences using @(see
svex-argmasks).</p>")

(local (xdoc::set-default-parents 4vmask))

(define 4vmask-p (x)
  :short "Recognizer for @(see 4vmask)s."
  :returns bool
  (sparseint-p x)
  ///
  (defthm 4vmask-p-compound-recognizer
    (implies (4vmask-p x)
             (or (integerp x)
                 (consp x)))
    :hints(("Goal" :in-theory (enable sparseint-p bitops::sparseint$-p)))
    :rule-classes :compound-recognizer)

  (defthm sparseint-p-when-4vmask-p
    (implies (4vmask-p x)
             (sparseint-p x)))

  (defthm 4vmask-p-when-sparseint-p
    (implies (sparseint-p x)
             (4vmask-p x))))

(define 4vmask-fix ((x 4vmask-p))
  :short "Fixing function for @(see 4vmask)s."
  :long "<p>This is unlike @(see ifix) because we return -1 (``all bits are
relevant'') in the default case.</p>"
  :returns (x-fix 4vmask-p :rule-classes (:rewrite :type-prescription))
  :inline t
  (mbe :logic (if (4vmask-p x) x -1)
       :exec x)
  ///
  (defthm 4vmask-fix-when-4vmask-p
    (implies (4vmask-p x)
             (equal (4vmask-fix x) x))))

(defsection 4vmask-equiv
  :short "Equivalence up to @(see 4vmask-fix)."
  (deffixtype 4vmask
    :pred 4vmask-p
    :fix 4vmask-fix
    :equiv 4vmask-equiv
    :define t
    :forward t))

(define 4vec-mask
  :short "Reduce a constant @(see 4vec) using a @(see 4vmask); any irrelevant
          bits become Xes."
  ((mask  4vmask-p "Mask of bits that we care about.")
   (value 4vec-p   "Original value to be masked."))
  :returns (masked-value 4vec-p "@('value') with irrelevant bits replaced by Xes.")
  (b* ((mask (sparseint-val (4vmask-fix mask)))
       ((4vec value) value))
    (4vec (logior (lognot mask) value.upper)
          (logand mask value.lower)))
  ///
  (deffixequiv 4vec-mask)

  (defthm 4vec-mask-idempotent
    (equal (4vec-mask mask (4vec-mask mask value))
           (4vec-mask mask value)))

  (defthm 4vec-mask-minus-1
    (equal (4vec-mask -1 value)
           (4vec-fix value))
    :hints(("Goal" :in-theory (enable 4vec-mask 4vec-equiv))))

  (defthm 4vec-mask-zero
    (equal (4vec-mask 0 value)
           (4vec-x))
    :hints(("Goal" :in-theory (enable 4vec-mask 4vec-equiv)))))

(define 4vec-mask-to-zero
  :short "Reduce a constant @(see 4vec) using a @(see 4vmask); any irrelevant
          bits become 0s."
  ((mask  4vmask-p "Mask of bits that we care about.")
   (value 4vec-p   "Original value to be masked."))
  :returns (masked-value 4vec-p "@('value') with irrelevant bits replaced by 0s.")
  (b* ((mask (sparseint-val (4vmask-fix mask)))
       ((4vec value) value))
    (4vec (logand mask value.upper)
          (logand mask value.lower)))
  ///
  (deffixequiv 4vec-mask-to-zero)

  (defthm 4vec-mask-to-zero-idempotent
    (equal (4vec-mask-to-zero mask (4vec-mask-to-zero mask value))
           (4vec-mask-to-zero mask value)))

  (defthm 4vec-mask-to-zero-minus-1
    (equal (4vec-mask-to-zero -1 value)
           (4vec-fix value))
    :hints(("Goal" :in-theory (enable 4vec-mask-to-zero 4vec-equiv))))

  (defthm 4vec-mask-to-zero-zero
    (equal (4vec-mask-to-zero 0 value)
           0)
    :hints(("Goal" :in-theory (enable 4vec-mask-to-zero 4vec-equiv))))


  (defthm 4vec-mask-of-4vec-mask-to-zero
    (equal (4vec-mask mask (4vec-mask-to-zero mask value))
           (4vec-mask mask value))
    :hints(("Goal" :in-theory (enable 4vec-mask))
           (logbitp-reasoning))))



(define 4vmask-empty ((x 4vmask-p))
  :short "@(call 4vmask-empty) recognizes the empty @(see 4vmask)."
  :inline t
  :enabled t
  (sparseint-equal (4vmask-fix x) 0))

(define 4vmask-subsumes ((x 4vmask-p) (y 4vmask-p))
  :short "@(call 4vmask-subsumes) checks whether the @(see 4vmask) @('x') cares
about strictly more bits than @('y') cares about."
  :returns (subsumesp booleanp :rule-classes :type-prescription)
  :inline t
  (not (sparseint-test-bitandc1 (4vmask-fix x) (4vmask-fix y)))
  ///
  (deffixequiv 4vmask-subsumes)

  (defthm 4vmask-subsumes-implies-masks-equal
    (implies (and (4vmask-subsumes m1 m2)
                  (equal (4vec-mask m1 x) (4vec-mask m1 y)))
             (equal (equal (4vec-mask m2 x) (4vec-mask m2 y))
                    t))
    :hints(("Goal" :in-theory (enable 4vec-mask))
           (acl2::logbitp-reasoning :prune-examples nil)))

  (defthmd 4vmask-subsumes-neg-1-implies-fixes
    (implies (and (4vmask-subsumes m1 -1)
                  (equal (4vec-mask m1 x) (4vec-mask m1 y)))
             (equal (equal (4vec-fix x) (4vec-fix y))
                    t))
    :hints(("Goal" :use ((:instance 4vmask-subsumes-implies-masks-equal
                          (m2 -1)))
            :in-theory (disable 4vmask-subsumes-implies-masks-equal))))

  (defthm 4vmask-subsumes-trans-1
    (implies (and (4vmask-subsumes a b)
                  (4vmask-subsumes b c))
             (4vmask-subsumes a c))
    :hints ((acl2::logbitp-reasoning)))

  (defthm 4vmask-subsumes-trans-2
    (implies (and (4vmask-subsumes b c)
                  (4vmask-subsumes a b))
             (4vmask-subsumes a c))
    :hints ((acl2::logbitp-reasoning)))

  (defthm 4vmask-subsumes-self
    (4vmask-subsumes x x)))

(define 4vmask-union ((x 4vmask-p) (y 4vmask-p))
  :short "@(call 4vmask-union) unions the @(see 4vmask)s @('x') and @('y'),
creating a new mask that includes all bits that are relevant for in either
@('x') or @('y')."
  :returns (union 4vmask-p :rule-classes :type-prescription)
  :inline t
  (sparseint-bitor (4vmask-fix x)
                   (4vmask-fix y))
  ///
  (deffixequiv 4vmask-union)

  (local (in-theory (enable 4vmask-subsumes)))

  (defthm 4vmask-subsumes-of-4vmask-union-1
    (4vmask-subsumes (4vmask-union x y) x)
    :hints ((acl2::logbitp-reasoning)))

  (defthm 4vmask-subsumes-of-4vmask-union-2
    (4vmask-subsumes (4vmask-union x y) y)
    :hints ((acl2::logbitp-reasoning))))

(deflist 4vmasklist
  :elt-type 4vmask-p
  :true-listp t)

(define 4veclist-mask
  :short "Reduce a list of constant @(see 4vec)s using individual @(see
          4vmask)s; any irrelevant bits become Xes."
  ((masks  4vmasklist-p "List of @(see 4vmask)s to use.")
   (values 4veclist-p   "List of @(see 4vec)s to simplify."))
  :returns (masked-values 4veclist-p "Updated @(see 4vec)s with irrelevant bits replaced by Xes.")
  ;; BOZO probably should add a same-lengthp guard?
  (cond ((atom values)
         nil)
        ((atom masks)
         (4veclist-fix values))
        (t
         (cons (4vec-mask (car masks) (car values))
               (4veclist-mask (cdr masks) (cdr values)))))
  ///
  (deffixequiv 4veclist-mask)

  (defthm len-of-4veclist-mask
    (equal (len (4veclist-mask masks values))
           (len values)))

  (defthm 4veclist-mask-of-nil
    (equal (4veclist-mask nil x)
           (4veclist-fix x))
    :hints(("Goal" :in-theory (enable 4veclist-mask 4veclist-fix))))

  (defthm equal-of-4veclist-mask-cons
    (equal (equal (4veclist-mask (cons m1 m) x)
                  (4veclist-mask (cons m1 m) y))
           (and (equal (consp x) (consp y))
                (equal (4vec-mask m1 (car x))
                       (4vec-mask m1 (car y)))
                (equal (4veclist-mask m (cdr x))
                       (4veclist-mask m (cdr y)))))
    :hints(("Goal" :in-theory (enable 4veclist-mask)))))


(define 4vmasklist-subsumes ((x 4vmasklist-p) (y 4vmasklist-p))
  :short "@(call 4vmasklist-subsumes) checks whether the masks in the list
@('x') all subsume the corresponding masks in @('y'), in the sense of @(see
4vmask-subsumes)."
  :measure (+ (len x) (len y))
  (if (and (atom x) (atom y))
      t
    (and (4vmask-subsumes (if (consp x) (car x) -1)
                          (if (consp y) (car y) -1))
         (4vmasklist-subsumes (cdr x) (cdr y))))
  ///
  (deffixequiv 4vmasklist-subsumes)

  (local (defun ind (x y m1 m2)
           (declare (xargS :measure (+ (len m1) (len m2))))
           (if (and (atom m1) (atom m2))
               (list x y)
             (ind (cdr x) (cdr y) (cdr m1) (cdr m2)))))

  (defthm 4vmasklist-subsumes-implies-masks-equal
    (implies (and (4vmasklist-subsumes m1 m2)
                  (equal (4veclist-mask m1 x) (4veclist-mask m1 y)))
             (equal (equal (4veclist-mask m2 x) (4veclist-mask m2 y))
                    t))
    :hints(("Goal" :in-theory (enable 4vmask-subsumes-neg-1-implies-fixes
                                      4veclist-mask
                                      4veclist-fix)
            :induct (ind x y m1 m2))))

  (defthm 4vmasklist-subsumes-self
    (4vmasklist-subsumes x x)
    :hints (("goal" :induct (len x)))))


(defalist 4vmask-alist
  :key-type svar
  :val-type 4vmask-p
  :true-listp t)

(define 4vmask-assoc
  :parents (4vmask-alist)
  :short "Slow function to look up the @(see 4vmask) for a variable in a @(see
          4vmask-alist), with proper @(see fty-discipline)."
  ((var   svar-p         "Variable to look up.")
   (alist 4vmask-alist-p "Alist to look it up in."))
  :returns (mask 4vmask-p :rule-classes :type-prescription
                 "Mask for this variable.")
  :long "<p>Any unbound variables are treated as having mask @('-1'), i.e., all
         bits are considered relevant.</p>"
  :prepwork ((local (in-theory (enable 4vmask-alist-p)))
             (local (defthm assoc-equal-is-hons-assoc-equal-when-4vmask-alist-p
                      (implies (4vmask-alist-p x)
                               (equal (assoc-equal k x)
                                      (hons-assoc-equal k x))))))
  (mbe :logic (4vmask-fix (cdr (hons-assoc-equal (svar-fix var) (4vmask-alist-fix alist))))
       :exec (let ((look (assoc-equal (svar-fix var) (4vmask-alist-fix alist))))
                (if look
                    (cdr look)
                  -1)))
  ///
  (deffixequiv 4vmask-assoc)

  (defthm 4vmask-assoc-of-nil
    (equal (4vmask-assoc var nil) -1)))

(define 4vmask-acons
  :parents (4vmask-alist)
  :short "Extend a slow @(see 4vmask-alist) with a new binding."
  ((var   svar-p         "Variable to bind.")
   (mask  4vmask-p       "Mask to bind it to.")
   (alist 4vmask-alist-p "Initial alist to extend."))
  :returns (extended-alist 4vmask-alist-p)
  :prepwork ((local (in-theory (enable 4vmask-alist-p))))
  (mbe :logic (cons (cons (svar-fix var) (4vmask-fix mask))
                    (4vmask-alist-fix alist))
       :exec (acons var mask alist))
  ///
  (deffixequiv 4vmask-acons)

  (defthm 4vmask-assoc-of-4vmask-acons
    (equal (4vmask-assoc j (4vmask-acons k v x))
           (if (svar-equiv j k)
               (4vmask-fix v)
             (4vmask-assoc j x)))
    :hints(("Goal" :in-theory (enable 4vmask-assoc)))))


(define 4vec-mask? ((mask 4vmask-p)
                    (care 4vec-p)
                    (dontcare 4vec-p))
  :returns (res 4vec-p)
  (b* (((4vec care))
       ((4vec dontcare))
       (mask (sparseint-val (4vmask-fix mask))))
    (4vec (logite mask care.upper dontcare.upper)
          (logite mask care.lower dontcare.lower)))
  ///
  (defthm 4vec-mask?-same
    (equal (4vec-mask? mask x x)
           (4vec-fix x))
    :hints((logbitp-reasoning)))

  (defthm 4vec-mask?-of-4vec-mask?
    (equal (4vec-mask? mask x (4vec-mask? mask y z))
           (4vec-mask? mask x z))
    :hints((logbitp-reasoning)
           (and stable-under-simplificationp
                '(:bdd (:vars nil)))))

  (defthm 4vec-mask?-of-4vec-mask
    (equal (4vec-mask? mask b (4vec-mask mask b))
           (4vec-mask mask b))
    :hints(("Goal" :in-theory (enable 4vec-mask))
           (logbitp-reasoning)))

  (defthm 4vec-mask-of-4vec-mask?
    (equal (4vec-mask mask (4vec-mask? mask a b))
           (4vec-mask mask a))
    :hints(("Goal" :in-theory (enable 4vec-mask))
           (logbitp-reasoning)))

  (defthm equal-of-4vec-mask?-when-equal-under-mask
    (equal (equal x (4vec-mask? mask y x))
           (and (4vec-p x)
                (equal (4vec-mask mask x) (4vec-mask mask y))))
    :hints(("Goal" :in-theory (enable 4vec-mask))
           (logbitp-reasoning)))

  ;; (defthm equal-of-4vec-mask?-when-equal-under-mask-hide
  ;;   (implies (and (equal (4vec-mask mask x) (4vec-mask mask y))
  ;;                 (4vec-p x))
  ;;            (equal (equal x (4vec-mask? mask y x)) t))
  ;;   :hints (("goal" :expand ((:free (x) (hide x)))
  ;;            :in-theory (disable 4vec-mask?))))

  (defthm 4vec-mask?-constants
    (and (equal (4vec-mask? -1 care dontcare) (4vec-fix care))
         (equal (4vec-mask? 0 care dontcare) (4vec-fix dontcare)))))

(define 4veclist-mask? ((masks 4vmasklist-p)
                        (care 4veclist-p)
                        (dontcare 4veclist-p))
  :guard (and (equal (len masks) (len care))
              (equal (len masks) (len dontcare)))
  (if (atom masks)
      nil
    (cons (4vec-mask? (car masks) (car care) (car dontcare))
          (4veclist-mask? (cdr masks) (cdr care) (cdr dontcare)))))

(defmacro 4vec-mask-equiv (lhs rhs mask)
  `(let ((lhs ,lhs))
     (equal lhs
            (4vec-mask? ,mask
                        ,rhs
                        (hide lhs)))))

(defmacro 4veclist-mask-equiv (lhs rhs masks)
  `(let ((lhs ,lhs))
     (equal lhs
            (4veclist-mask? ,masks
                            ,rhs
                            (hide lhs)))))

