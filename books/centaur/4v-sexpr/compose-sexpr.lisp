; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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

; compose-sexpr.lisp
; Original author: Sol Swords <sswords@centtech.com>
;
; This is for a theorem about a block that looks like this
;
;
;     +================================================+
;     \                                  +====+        \
;     \  +---------------------->+ b2ins \    \ out2   \
;     \  |                       |------>\blk2\---->+  \
; --->\--|     +====+            |       \    \     |  \ outs
; ins \  |     \    \ b1out +--->+       \    \     |->\------
;     \  |ins1 \blk1\------>|            +====+     |  \
;     \  +---->\    \       |                       |  \
;     \        \    \       +---------------------->+  \
;     \        +====+                                  \
;     +================================================+
;
; Here any fork in the signals allows overlap between the two branches -- e.g.,
; some signals in b1out may be routed to both the blk2 inputs and to the
; output.  However, any merge between signals requires that the two incoming
; sets be disjoint -- e.g. because signals form out2 and b1out merge to form
; outs, out2 and b1out may not contain the same signals.

(in-package "ACL2")
(include-book "bitspecs")
(include-book "sexpr-to-faig")
(include-book "sexpr-advanced")
(include-book "centaur/misc/hons-extra" :dir :system)

(defund marker (x) (declare (ignore x)) t)

(in-theory (disable marker (marker) (:type-prescription marker)))


(encapsulate
  ;; -spec-: alist specs, which describe how to convert a set of "formatted"
  ;; data (numbers, Booleans, etc) into an alist mapping variables to booleans,
  ;; and back.  Also specifies what kind of inputs these must be and what
  ;; names must be bound in the alist.
  (((cmp4v-spec-ins) => *)
   ((cmp4v-spec-ins1) => *)
   ((cmp4v-spec-b1out) => *)
   ((cmp4v-spec-b2ins) => *)
   ((cmp4v-spec-out) => *)
   ((cmp4v-spec-out2) => *)
   ;; -exprs-: alist mapping names to 4v-sexprs
   ((cmp4v-exprs-blk1) => *)
   ((cmp4v-exprs-blk2) => *)
   ((cmp4v-exprs-whole) => *)
   ;; -hyp: requirements about the formatted data
   ;; -prop: goal to be proved about formatted data
   ((cmp4v-blk1-hyp *) => *)
   ((cmp4v-blk2-hyp *) => *)
   ((cmp4v-blk1-prop * *) => *)
   ((cmp4v-blk2-prop * *) => *)
   ((cmp4v-whole-hyp *) => *)
   ((cmp4v-whole-prop * *) => *))

  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)

  (local
   (progn
     (defun cmp4v-spec-ins () nil)
     (defun cmp4v-spec-ins1 () nil)
     (defun cmp4v-spec-b1out () nil)
     (defun cmp4v-spec-b2ins () nil)
     (defun cmp4v-spec-out () nil)
     (defun cmp4v-spec-out2 () nil)
     (defun cmp4v-exprs-blk1 () nil)
     (defun cmp4v-exprs-blk2 () nil)
     (defun cmp4v-exprs-whole () nil)
     (defun cmp4v-blk1-hyp (ins1) nil)
     (defun cmp4v-blk2-hyp (b2ins) nil)
     (defun cmp4v-blk1-prop (ins1 b1out) t)
     (defun cmp4v-blk2-prop (b2ins out2) t)
     (defun cmp4v-whole-hyp (ins) nil)
     (defun cmp4v-whole-prop (ins out) t)))

  ;; These two constraints are likely provable by symbolic simulation:
  (defthm cmp4v-blk1-ok
    (implies (and
              (marker 'blk1-ok)
              ;; ins1 is a set of formatted inputs fitting the shape specified
              ;; by -spec-ins
              (params-for-4v-bitspecp (cmp4v-spec-ins1) ins1)
              ;; ins1 satisfy the hyp for blk1
              (cmp4v-blk1-hyp ins1))
             (b* ( ;; transform ins1 to an alist
                  (al (params-to-4v-alist (cmp4v-spec-ins1) ins1))
                  ;; evaluate the blk1 SEXPRs using the alist
                  (ev (4v-sexpr-eval-alist (cmp4v-exprs-blk1) al))
                  ;; transform that alist into formatted data according to
                  ;; -spec-ints
                  (b1out (4v-alist-to-params (cmp4v-spec-b1out) ev)))
               (and
                ;; The resulting formatted data fits the shape specified by -spec-ints
                (params-for-4v-bitspecp (cmp4v-spec-b1out) b1out)
                ;; The result satisfies the property required of blk1.
                (cmp4v-blk1-prop ins1 b1out)))))

  (defthm cmp4v-blk2-ok
    (implies (and
              (marker 'blk2-ok)
              ;; ins2 and ints are sets of formatted inputs fitting the shapes
              ;; specified by -spec-ins2 and -spec-ints, resp.
              (params-for-4v-bitspecp (cmp4v-spec-b2ins) b2ins)
              ;; ins2 and ints together satisfy the hyp for blk2
              (cmp4v-blk2-hyp b2ins))
             (b* ( ;; transform ints and ins2 to an alist
                  (al (params-to-4v-alist (cmp4v-spec-b2ins) b2ins))
                  ;; evaluate the blk2 SEXPRs using the alist
                  (ev (4v-sexpr-eval-alist (cmp4v-exprs-blk2) al))
                  ;; transform that alist into formatted data according to
                  ;; -spec-out2.
                  (out2 (4v-alist-to-params (cmp4v-spec-out2) ev)))
               (and
                ;; The resulting formatted data fits the shape specified by -spec-out2
                (params-for-4v-bitspecp (cmp4v-spec-out2) out2)
                ;; The result satisfies the property required of blk2.
                (cmp4v-blk2-prop b2ins out2)))))


  ;; These three might need some theorem proving:

  (defthm cmp4v-whole-hyp-impl-blk1-hyp
    ;; If the inputs are well-formed and the hyp for the whole block is
    ;; satisfied, then the hyp for blk1 is satisfied by the extraction of the
    ;; blk1 inputs.
    (implies (and (marker 'hyp-implies-blk1-hyp)
                  (cmp4v-whole-hyp ins)
                  (params-for-4v-bitspecp (cmp4v-spec-ins) ins))
             (cmp4v-blk1-hyp
              (4v-alist-to-params
               (cmp4v-spec-ins1)
               (params-to-4v-alist
                (cmp4v-spec-ins) ins)))))

  (defthm cmp4v-blk1-prop-implies-blk2-hyp
    ;; If the hyp for the whole thing and for blk1 are both satisfied and the
    ;; inputs and cut signals are of the right shape, then the blk2 hyp is
    ;; satisfied.
    (implies
     (marker 'prop1-implies-blk2-hyp)
     (let* ((ins1 (4v-alist-to-params
                   (cmp4v-spec-ins1)
                   (params-to-4v-alist
                    (cmp4v-spec-ins) ins)))
            (b2ins (4v-alist-to-params
                    (cmp4v-spec-b2ins)
                    (append (params-to-4v-alist (cmp4v-spec-b1out) b1out)
                            (params-to-4v-alist (cmp4v-spec-ins) ins)))))
       (implies (and (cmp4v-whole-hyp ins)
                     (cmp4v-blk1-prop ins1 b1out)
                     (params-for-4v-bitspecp (cmp4v-spec-ins) ins)
                     (params-for-4v-bitspecp (cmp4v-spec-b1out) b1out))
                (cmp4v-blk2-hyp b2ins)))))

  (defthm cmp4v-blk1-and-blk2-props-imply-whole
    ;; If the blk1 and blk2 props are satisfied, all the data is of the right
    ;; shapes, and the hyp for the whole thing is satisfied, then the goal
    ;; property is satisfied.
    (implies
     (marker 'props-imply-whole)
     (let* ((ins1 (4v-alist-to-params
                  (cmp4v-spec-ins1)
                  (params-to-4v-alist
                   (cmp4v-spec-ins) ins)))
            (b2ins (4v-alist-to-params
                    (cmp4v-spec-b2ins)
                    (append (params-to-4v-alist (cmp4v-spec-b1out) b1out)
                            (params-to-4v-alist (cmp4v-spec-ins) ins))))
            (outs (4v-alist-to-params
                   (cmp4v-spec-out)
                   (append (params-to-4v-alist
                            (cmp4v-spec-b1out) b1out)
                           (params-to-4v-alist
                            (cmp4v-spec-out2) out2)))))
       (implies (and (params-for-4v-bitspecp (cmp4v-spec-ins) ins)
                     (params-for-4v-bitspecp (cmp4v-spec-b1out) b1out)
                     (params-for-4v-bitspecp (cmp4v-spec-out2) out2)
                     (cmp4v-whole-hyp ins)
                     (cmp4v-blk1-prop ins1 b1out)
                     (cmp4v-blk2-prop b2ins out2))
                (cmp4v-whole-prop ins outs)))))


  (defthm cmp4v-sexprs-whole-are-composition
    ;; SEXPR composition of blk1 and blk2 gives the whole block
    (implies (marker 'sexprs-are-composition)
             (4v-sexpr-alist-equiv
              (cmp4v-exprs-whole)
              (make-fast-alist
               (4v-sexpr-alist-extract
                (alist-keys (cmp4v-exprs-whole))
                (make-fast-alist
                 (append (cmp4v-exprs-blk1)
                         (4v-sexpr-restrict-alist
                          (cmp4v-exprs-blk2)
                          (make-fast-alist (cmp4v-exprs-blk1))))))))))

  (defthm cmp4v-misc-reqs
    (implies (marker 'misc-reqs)
             (and
              ;; The input variables used in the blk1 SEXPRs are a subset of the variables
              ;; mentioned in -spec-ins1
              (hons-subset (4v-sexpr-vars-list (alist-vals (cmp4v-exprs-blk1)))
                           (4v-bitspec-vars (cmp4v-spec-ins1)))
              ;; The input variables used in the blk2 SEXPRs are a subset of
              ;; the variables mentioned in b2ins.
              (hons-subset (4v-sexpr-vars-list (alist-vals (cmp4v-exprs-blk2)))
                           (4v-bitspec-vars (cmp4v-spec-b2ins)))

              ;; The variables of b1out are a subset of the keys of exprs-blk1
              (hons-subset (4v-bitspec-vars (cmp4v-spec-b1out))
                           (alist-keys (cmp4v-exprs-blk1)))

              ;; The variables of out2 are a subset of the keys of exprs-blk2
              (hons-subset (4v-bitspec-vars (cmp4v-spec-out2))
                           (alist-keys (cmp4v-exprs-blk2)))

              ;; The keys of exprs-whole are a superset of the vars of spec-out.
              (hons-subset (4v-bitspec-vars (cmp4v-spec-out))
                           (alist-keys (cmp4v-exprs-whole)))

              ;; No duplicate signals between the inputs and the outputs of blk1
              (not (hons-intersect-p (alist-keys (cmp4v-exprs-blk1))
                                     (4v-bitspec-vars (cmp4v-spec-ins))))

              ;; No duplicate signals between the outputs of blk1 and the
              ;; outputs of blk2
              (not (hons-intersect-p (alist-keys (cmp4v-exprs-blk1))
                                     (alist-keys (cmp4v-exprs-blk2))))

              ;; No duplicate signals between the inputs and the outputs of blk2
              (not (hons-intersect-p (alist-keys (cmp4v-exprs-blk2))
                                     (4v-bitspec-vars (cmp4v-spec-ins))))

              ;; The input bitspec for block1 is a subset of the full
              ;; input bitspec
              (hons-subset (hons-copy (cmp4v-spec-ins1))
                           (hons-copy (cmp4v-spec-ins)))

              ;; The block2 input bitspec is a subset of the union of the ins
              ;; and b1out bitspecs
              (hons-subset (hons-copy (cmp4v-spec-b2ins))
                           (hons-copy (append (cmp4v-spec-ins)
                                              (cmp4v-spec-b1out))))

              ;; The output bitspec is a subset of the union of the outputs
              ;; from the two blocks.
              (hons-subset (hons-copy (cmp4v-spec-out))
                           (hons-copy (append (cmp4v-spec-b1out)
                                              (cmp4v-spec-out2))))

              ;; No duplicate names in the internal signals or inputs
              (not (hons-dups-p (4v-bitspec-vars (cmp4v-spec-ins))))
              (not (hons-dups-p (4v-bitspec-vars (cmp4v-spec-ins1))))
              (not (hons-dups-p (4v-bitspec-vars (cmp4v-spec-out))))
              (not (hons-dups-p (4v-bitspec-vars (cmp4v-spec-out2))))
              (not (hons-dups-p (4v-bitspec-vars (cmp4v-spec-b1out))))
              (not (hons-dups-p (4v-bitspec-vars (cmp4v-spec-b2ins))))
              ;; All alist-specs are well-formed
              (4v-bitspecp (cmp4v-spec-ins))
              (4v-bitspecp (cmp4v-spec-ins1))
              (4v-bitspecp (cmp4v-spec-out))
              (4v-bitspecp (cmp4v-spec-out2))
              (4v-bitspecp (cmp4v-spec-b1out))
              (4v-bitspecp (cmp4v-spec-b2ins))))))



(local
 (progn
   (in-theory (enable 4v-alists-agree-to-4v-env-equiv))


   (defthm 4v-alists-agree-for-new-append-extract-lemma
     (implies (and (subsetp-equal keys (append xkeys (alist-keys b)))
                   (subsetp-equal xkeys (alist-keys a))
                   (not (intersectp-equal (alist-keys a) (alist-keys b))))
              (4v-alists-agree keys (append (4v-alist-extract xkeys a) b)
                               (append a b)))
     :hints (("goal" :do-not-induct t
              :in-theory (e/d ()
                              (4v-env-equiv-to-key-and-env-equiv
                               4v-fix)))
             (witness :ruleset 4v-env-equiv-witnessing)
             (and stable-under-simplificationp
                  '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys
                                     alists-compatible-hons-assoc-equal)
                                    (alist-keys-member-hons-assoc-equal
                                     4v-fix))))
             (set-reasoning)))


   (defthm 4v-sexpr-eval-alist-new-append-extract-lemma
     (implies (and (subsetp-equal (4v-sexpr-vars-list (alist-vals x))
                                  (append xkeys (alist-keys b)))
                   (subsetp-equal xkeys (alist-keys a))
                   (not (intersectp-equal (alist-keys a) (alist-keys b))))
              (equal (4v-sexpr-eval-alist x (append (4v-alist-extract xkeys a) b))
                     (4v-sexpr-eval-alist x (append a b))))
     :hints(("Goal" :in-theory (disable 4v-sexpr-eval))))


   (defthm 4v-alist-to-params-new-append-extract-lemma
     (implies (and (subsetp-equal (4v-bitspec-vars spec)
                                  (append xkeys (alist-keys b)))
                   (subsetp-equal xkeys (alist-keys a))
                   (not (intersectp-equal (alist-keys a) (alist-keys b))))
              (equal (4v-alist-to-params spec (append (4v-alist-extract xkeys a) b))
                     (4v-alist-to-params spec (append a b))))
     :hints(("Goal" :in-theory (e/d
                                (4v-alist-to-params-when-4v-alists-agree-rw)
                                (4v-alist-to-params)))))






   (defthm 4v-alists-agree-4v-alist-extract
     (implies (subsetp-equal keys1 keys)
              (4v-alists-agree keys1 (4v-alist-extract keys a) a))
     :hints (("goal" :do-not-induct t
              :in-theory (disable 4v-env-equiv-to-key-and-env-equiv
                                  4v-fix))
             (witness :ruleset 4v-env-equiv-witnessing)
             (and stable-under-simplificationp
                  '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                    (alist-keys-member-hons-assoc-equal
                                     4v-fix))))
             (set-reasoning)
             (and stable-under-simplificationp
                  '(:in-theory (e/d (alist-keys-member-hons-assoc-equal)
                                    (hons-assoc-equal-iff-member-alist-keys
                                     4v-fix))))))

   (defthm 4v-sexpr-eval-alist-4v-alist-extract
     (implies (subsetp-equal (4v-sexpr-vars-list (alist-vals x))
                             keys)
              (equal (4v-sexpr-eval-alist x (4v-alist-extract keys a))
                     (4v-sexpr-eval-alist x a)))
     :hints(("Goal" :in-theory (disable 4v-sexpr-eval))))


   (defthm 4v-alist-to-params-4v-alist-extract
     (implies (subsetp-equal (4v-bitspec-vars spec) keys)
              (equal (4v-alist-to-params spec (4v-alist-extract keys a))
                     (4v-alist-to-params spec a)))
     :hints (("goal" :in-theory (e/d (4v-alist-to-params-when-4v-alists-agree-rw)
                                     (4v-alists-agree-to-4v-env-equiv)))))


   (defthm 4v-alist-for-bitspecp-4v-alist-extract
     (implies (subsetp-equal (4v-bitspec-vars spec) keys)
              (equal (4v-alist-for-bitspecp spec (4v-alist-extract keys a))
                     (4v-alist-for-bitspecp spec a)))
     :hints (("goal" :in-theory (e/d (4v-alist-for-bitspecp-when-4v-alists-agree-rw)
                                     (4v-alists-agree-to-4v-env-equiv)))))



   (defthm 4v-sexpr-eval-alist-4v-sexpr-alist-extract
     (equal (4v-sexpr-eval-alist (4v-sexpr-alist-extract keys al) env)
            (4v-alist-extract keys (4v-sexpr-eval-alist al env))))









   (defthm 4v-alist-for-bitspec-entryp-when-member2
     (implies (and (member-equal x spec)
                   (4v-alist-for-bitspecp spec alist))
              (4v-alist-for-bitspec-entryp x alist))
     :hints(("Goal" :in-theory (e/d (member-equal)
                                    (4v-alist-for-bitspec-entryp)))))

   (defthm 4v-alist-for-bitspecp-when-subset
     (implies (and (subsetp-equal spec1 spec)
                   (4v-alist-for-bitspecp spec alist))
              (4v-alist-for-bitspecp spec1 alist))
     :hints(("Goal" :in-theory (e/d (subsetp-equal)
                                    (4v-alist-for-bitspec-entryp)))))



   (defthm 4v-alists-agree-append-extract-second
     (implies (subsetp-equal keys
                             (append (alist-keys al1) keys2))
              (4v-alists-agree keys (append al1 (4v-alist-extract keys2 al2))
                               (append al1 al2)))
     :hints (("goal" :in-theory (e/d (hons-assoc-equal-iff-member-alist-keys
                                      hons-assoc-equal-when-not-member-alist-keys)
                                     (4v-alists-agree-to-4v-env-equiv
                                      4v-fix
                                      alist-keys-member-hons-assoc-equal))
              :do-not-induct t)
             (witness :ruleset (4v-alists-agree-witnessing
                                4v-alists-agree-4v-lookup-ex))
             (witness :ruleset set-reasoning-no-consp)))

   (defthm 4v-sexpr-eval-alist-append-extract-second
     (implies (subsetp-equal (4v-sexpr-vars-list (alist-vals x))
                             (append (alist-keys al1) keys2))
              (equal (4v-sexpr-eval-alist x (append al1 (4v-alist-extract keys2 al2)))
                     (4v-sexpr-eval-alist x (append al1 al2))))
     :hints(("Goal" :in-theory (disable 4v-sexpr-eval))))

   (defthm 4v-alist-to-params-append-extract-second
     (implies (subsetp-equal (4v-bitspec-vars spec)
                             (append (alist-keys al1) keys2))
              (equal (4v-alist-to-params spec (append al1 (4v-alist-extract keys2 al2)))
                     (4v-alist-to-params spec (append al1 al2))))
     :hints(("Goal" :in-theory (e/d (4v-alist-to-params-when-4v-alists-agree-rw)
                                    (4v-alist-to-params)))))


   (defthm 4v-alist-for-bitspecp-append-when-first-covers
     (implies (subsetp-equal (4v-bitspec-vars spec)
                             (alist-keys a))
              (equal (4v-alist-for-bitspecp spec (append a b))
                     (4v-alist-for-bitspecp spec a)))
     :hints(("Goal" :in-theory (e/d (4v-alist-for-bitspecp-when-4v-alists-agree-rw)
                                    (4v-alist-for-bitspec-entryp append)))))


   (defthm bitspec-member-var-subsets
     (implies (member-equal a b)
              (subsetp-equal (4v-bitspec-entry-vars a) (4v-bitspec-vars b)))
     :hints(("Goal" :in-theory (e/d (subsetp-equal 4v-bitspec-vars)
                                    (4v-bitspec-entry-vars)))))

   (defthm bitspec-subsets-vars-subsets
     (implies (subsetp-equal a b)
              (subsetp-equal (4v-bitspec-vars a) (4v-bitspec-vars b)))
     :hints(("Goal" :in-theory (e/d (subsetp-equal 4v-bitspec-vars)
                                    (4v-bitspec-entry-vars)))))



   (defthm 4v-bitspec-vars-append
     (equal (4v-bitspec-vars (append a b))
            (append (4v-bitspec-vars a) (4v-bitspec-vars b)))
     :hints(("Goal" :in-theory (disable 4v-bitspec-entry-vars))))


   (defthm cmp4v-blk2-vars-subset-of-ints-and-ins2
     (subsetp-equal (4v-sexpr-vars-list (alist-vals (cmp4v-exprs-blk2)))
                    (append (4v-bitspec-vars (cmp4v-spec-b1out))
                            (4v-bitspec-vars (cmp4v-spec-ins))))
     :hints (("goal" :use ((:instance bitspec-subsets-vars-subsets
                                      (a (cmp4v-spec-b2ins))
                                      (b (append (cmp4v-spec-b1out)
                                                 (cmp4v-spec-ins))))
                           cmp4v-misc-reqs)
              :in-theory (e/d (marker)
                              (bitspec-subsets-vars-subsets
                               cmp4v-misc-reqs)))))


   (defthm subsetp-equal-bitspec-vars-append
     (implies (subsetp-equal a (append b c))
              (subsetp-equal (4v-bitspec-vars a)
                             (append (4v-bitspec-vars b)
                                     (4v-bitspec-vars c))))
     :hints (("goal" :use ((:instance bitspec-subsets-vars-subsets
                                      (b (append b c)))))))

   (defthm cmp4v-vars-out-subset-of-b1out-and-out2
     (subsetp-equal (4v-bitspec-vars (cmp4v-spec-out))
                    (append (4v-bitspec-vars (cmp4v-spec-b1out))
                            (4v-bitspec-vars (cmp4v-spec-out2))))
     :hints (("goal" :use cmp4v-misc-reqs
              :in-theory (e/d (marker) (cmp4v-misc-reqs)))))

   (defthm cmp4v-vars-of-out-subset-of-blk1-out2
     (subsetp-equal (4v-bitspec-vars (cmp4v-spec-out))
                    (append (alist-keys (cmp4v-exprs-blk1))
                            (4v-bitspec-vars (cmp4v-spec-out2))))
     :hints (("goal" :use cmp4v-misc-reqs
              :in-theory (e/d (marker) (cmp4v-misc-reqs)))))


   (defthm out2-vars-not-intersecting-blk1-keys
     (not (intersectp-equal (4v-bitspec-vars (cmp4v-spec-out2))
                            (alist-keys (cmp4v-exprs-blk1))))
     :hints (("goal" :use cmp4v-misc-reqs
              :in-theory (e/d (marker) (cmp4v-misc-reqs)))
             (witness :ruleset set-reasoning-no-consp)))



   (defthm cmp4v-b1out-vars-not-intersecting-ins
     (not (intersectp-equal (4v-bitspec-vars (cmp4v-spec-b1out))
                            (4v-bitspec-vars (cmp4v-spec-ins))))
     :hints (("goal" :use cmp4v-misc-reqs
              :in-theory (e/d ((marker))
                              (cmp4v-misc-reqs)))
             (set-reasoning)))

   (in-theory (e/d* ()
                    (4v-sexpr-eval-alist
                     sets::double-containment
                     4v-fix 4vp
                     4v-alist-to-params
                     4v-bitspec-vars
                     4v-bitspec-entry-vars
                     params-to-4v-alist
                     (:rules-of-class :type-prescription :here)
                     no-duplicatesp-equal-non-cons
                     4v-alist-extract not
                     4v-bitspecp
                     no-duplicatesp-equal
                     subsetp-when-atom-left
                     append 4v-sexpr-alist-extract
                     subsetp-trans
                     intersectp-equal-non-cons-1
                     intersectp-equal-non-cons
                     4v-sexpr-vars-list
                     4v-sexpr-restrict-alist
                     alist-equiv-append-atom
                     alist-vals-when-atom
                     alist-keys-when-atom
                     4v-alist-to-params-append-when-first-does-not-intersect-vars
                     4v-alist-for-bitspecp
                     params-for-4v-bitspecp)
                    ((:type-prescription 4v-bitspec-vars))))))

;; BOZO fix up the above thms so that this isnt' necessary
(local (in-theory (disable COMMUTATIVITY-OF-APPEND-UNDER-SET-EQUIV)))


(defthm cmp4v-generic-theorem
  (implies (and
            ;; The formatted input vector, ins, is of the form dictated by
            ;; cmp4v-spec-ins.
            (params-for-4v-bitspecp (cmp4v-spec-ins) ins)
            ;; ins satisfies the top-level hyp
            (cmp4v-whole-hyp ins))
           (b* ( ;; Form the input alist for the whole block
                (al (params-to-4v-alist (cmp4v-spec-ins) ins))
                ;; Evaluate the whole block on the inputs
                (ev (4v-sexpr-eval-alist (cmp4v-exprs-whole)
                                         al))
                ;; Transform the result alist to formatted data
                (out (4v-alist-to-params (cmp4v-spec-out) ev)))
             (and
              ;; The results are of the format dictated by -spec-out2
              (params-for-4v-bitspecp (cmp4v-spec-out) out)
              ;; The results satisfy the top-level property.
              (cmp4v-whole-prop ins out))))


  :hints ((b* ((ins1 '(4v-alist-to-params
                       (cmp4v-spec-ins1)
                       (params-to-4v-alist (cmp4v-spec-ins) ins)))
               (b1out `(b* ((al (params-to-4v-alist (cmp4v-spec-ins1) ,ins1))
                            (ev (4v-sexpr-eval-alist (cmp4v-exprs-blk1) al)))
                         (4v-alist-to-params (cmp4v-spec-b1out) ev)))
               (b2ins `(4v-alist-to-params
                        (cmp4v-spec-b2ins)
                        (append (params-to-4v-alist (cmp4v-spec-b1out) ,b1out)
                                (params-to-4v-alist (cmp4v-spec-ins) ins))))
               (out2 `(b* ((al (params-to-4v-alist (cmp4v-spec-b2ins)
                                                   ,b2ins))
                           (ev (4v-sexpr-eval-alist (cmp4v-exprs-blk2) al)))
                        (4v-alist-to-params (cmp4v-spec-out2) ev))))
            `(:use (cmp4v-misc-reqs
                    (:instance
                     cmp4v-blk1-and-blk2-props-imply-whole
                     (out2 ,out2)  (b1out ,b1out))
                    (:instance cmp4v-blk2-ok (b2ins ,b2ins))
                    (:instance cmp4v-blk1-ok (ins1 ,ins1))
                    (:instance cmp4v-blk1-prop-implies-blk2-hyp
                               (b1out ,b1out)))
                   :in-theory (e/d (marker)
                                   (cmp4v-blk1-and-blk2-props-imply-whole
                                    cmp4v-blk2-ok
                                    cmp4v-blk1-ok
                                    cmp4v-blk1-prop-implies-blk2-hyp
                                    cmp4v-misc-reqs))
                   :do-not-induct t))))







