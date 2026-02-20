; FGL - A Symbolic Simulation Framework for ACL2
;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holder nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Author: Sol Swords <sol.swords@arm.com>

(in-package "FGL")

(include-book "fancy-ev")

(define annotate (arg x)
  (declare (ignore arg))
  :enabled t
  :parents (fgl-rewrite-rules)
  :short "Wrapper to mark a function call with some data for use by the FGL rewriter"
  :long "<p>Annotate is just a two-argument function that returns its second argument.
It is intended to be used to temporarily associate the data in its first
argument with the subterm in its second argument, such that rewrite rules can
treat that subterm differently based on whether it has an annotation and what
it contains.</p>

<p>Example: print some info about a call before going on to rewrite it as normal:</p>

@({
 (fgl::def-fgl-rewrite print-first-argument-of-my-fn
   (implies (and (fgl::bind-fn-annotation annot 'my-fn)
                 (not annot))
            (equal (my-fn a b)
                   (fgl::fgl-prog2
                    (fgl::syntax-interp (cw \"my-fn first arg: ~x0~%\" a))
                    (fgl::annotate :already-printed (my-fn a b))))))
 })

<p>Normally, a rule that included the unchanged LHS in the RHS would
loop. However, the RHS of the rule wraps an annotation around the LHS call, and
the hypotheses of this rule check that there is no annotation wrapped around
the call, so when trying this rule on the LHS occurrence in the RHS, it will
fail instead of looping.</p>

<p>The associated utility @(see bind-fn-annotation) binds to a variable the
annotation data from the annotation wrapped around the most recent (innermost)
call of the given function, or NIL if there was no annotation.</p>

<p>Another utility, @(see bind-nth-fn-annotation), similarly binds the
annotation from the nth-innermost call of the function. The following example
implements a simple way of tracing the rewriting of a function -- we check that
the current call of the function is not yet annotated, so that the rule doesn't
loop; then we look for a prior call of the function and get its annotation to
find the nesting depth to use for the tracing:</p>

@({
 (defun next-printed-annotation-index (old-annot)
   (case-match old-annot
     ((':printed n) (if (natp n) (+ 1 n) 0))
     (& 0)))

 (fgl::def-fgl-rewrite trace-my-fn
   (implies (and (fgl::bind-fn-annotation annot 'my-fn)
                 (not annot)
                 (fgl::bind-nth-fn-annotation old-annot 1 'my-fn)
                 (equal index (next-printed-annotation-index old-annot)))
            (equal (my-fn a b)
                   (fgl::fgl-prog2
                    (fgl::syntax-interp (cw \"~t0~x0> my-fn ~x1~%\" index a))
                    (let ((res (fgl::annotate `(:printed ,index) (my-fn a b))))
                      (fgl::fgl-prog2
                       (fgl::syntax-interp (cw \"~t0<~x0 my-fn ~x1~%\" index a))
                       res))))))
 })

<h3>Preserving Congruences</h3>

<p>A potential problem with the above uses of @('annotate') is that the call of
the function in the right-hand side of the rewrite rule doesn't allow rewriting
under any congruences other than @('equal'). If we want to rewrite the function
under a congruence such as @('iff'), the following example illustrates how to
change the invocation of @('annoate') and usage of @('bind-fn-annotation') to
allow this.</p>

@({
 (fgl::def-fgl-rewrite annotate-my-pred
   (implies (and (fgl::bind-fn-annotation annot 'my-pred :ignore-fns '(if))
                 (not annot))
            (iff (my-pred x y)
                 (let ((res (fgl::annotate '(:annotated) (and (my-pred x y) t))))
                  (fgl::fgl-prog2
                   (fgl::syntax-interp (cw \"my-pred: ~x0~%\" res))
                   res)))))
 })

<p>Similarly to rewrite under integer congruence:</p>
@({
 (fgl::def-fgl-rewrite annotate-my-idx
   (implies (and (fgl::bind-fn-annotation annot 'my-idx :ignore-fns '(ifix))
                 (not annot))
            (int-equiv (my-idx x y)
                       (let ((res (fgl::annotate '(:annotated) (ifix (my-idx x y)))))
                         (fgl::fgl-prog2
                          (fgl::syntax-interp (cw \"my-idx: ~x0~%\" res))
                          res)))))
 })

<h3>Looping due to IF test second-pass rewriting</h3>

<p>An annotation rule of the following form might loop despite the apparently
proper checking of the annotation in the hypothesis:</p>

@({
 (fgl::def-fgl-rewrite annotate-my-pred-bad
   (implies (and (fgl::bind-fn-annotation annot 'my-pred :ignore-fns '(if))
                 (not annot))
            (equal (my-pred x y)
                   (let ((res (and (fgl::annotate '(:annotated) (my-pred x y)) t)))
                     (fgl::fgl-prog2
                      (fgl::syntax-interp (cw \"my-pred: ~x0~%\" res))
                      res)))))

<p>This is because a second pass of rewriting is applied to an @('if') test
before it is entered into the Boolean variable database (see @(see
fgl-getting-bits-from-objects)). In more detail:</p>

<ol>
<li>On first rewriting a call of @('my-pred'), we attempt to apply @('annotate-my-pred-bad'); the annotation hyps are satisfied so we proceed to rewriting the RHS.</li>

<li>When rewriting the @('my-pred') call inside the @('annotate'),
re-application of @('annotate-my-pred-bad') is properly stopped by the @('(not
annot)') hyp. Suppose that this rewriting fails and yields the LHS
unchanged (or more generally, produces new term that also matches the left-hand
side pattern).</li>

<li>After that rewrite is finished, the @('annotate') call is rewritten with
the definition of @('annotate') (i.e. returning its second argument), so this
also produces the LHS unchanged.</li>

<li>Because of the second pass of rewriting applied to IF tests (recalling that
@('(and x t)') expands to @('(if x t nil)'), rewriting is again applied to the
top level of the resulting LHS term. Since we are now outside the call of
@('annotate'), the hyps of @('annotate-my-pred-bad') are again satisfied and it
can be applied again, completing the loop.</li>
</ol>

<p>To avoid such a loop, it is recommended to formulate such a rule like
@('annotate-my-pred'), i.e. with the @('annotate') call not in an @('iff')
congruence context. This can be accomplished by binding it in a
@('let'). Congruences needed for rewriting the inner call should be established
inside the @('annotate') call using fixing functions.</p>

"
  x)

(define interp-st-scan-for-fnsym ((n natp) (fn pseudo-fnsym-p) interp-st)
  :guard (<= n (interp-st-full-scratch-len interp-st))
  :measure (nfix (- (interp-st-full-scratch-len interp-st) (nfix n)))
  :returns (maybe-index acl2::maybe-natp :rule-classes :type-prescription)
  :guard-hints (("goal" :in-theory (enable stack$a-nth-scratch-kind
                                           stack$a-nth-scratch)))
  (if (mbe :logic (zp (- (interp-st-full-scratch-len interp-st) (nfix n)))
           :exec (eql n (interp-st-full-scratch-len interp-st)))
      nil
    (if (and (eq (interp-st-nth-scratch-kind n interp-st) :fnsym)
             (eq (interp-st-nth-scratch-fnsym n interp-st) (pseudo-fnsym-fix fn)))
        (lnfix n)
      (interp-st-scan-for-fnsym (1+ (lnfix n)) fn interp-st)))
  ///
  (defret <fn>-bound
    (implies maybe-index
             (< maybe-index (interp-st-full-scratch-len interp-st)))
    :rule-classes :linear))

(define interp-st-debug-stack ((count natp) (n natp) interp-st)
  :guard (<= n (interp-st-full-scratch-len interp-st))
  :measure (nfix count)
  :guard-hints (("goal" :in-theory (enable stack$a-nth-scratch-kind
                                           stack$a-nth-scratch)))
  (if (or (zp count)
          (mbe :logic (zp (- (interp-st-full-scratch-len interp-st) (nfix n)))
               :exec (eql n (interp-st-full-scratch-len interp-st))))
      nil
    (cons (let ((kind (interp-st-nth-scratch-kind n interp-st)))
            (cons kind (and (eq kind :fnsym)
                            (interp-st-nth-scratch-fnsym n interp-st))))
          (interp-st-debug-stack (1- count) (1+ (lnfix n)) interp-st))))

(define interp-st-scan-for-nth-fnsym-occ ((idx natp) (n natp) (fn pseudo-fnsym-p) interp-st)
  :guard (<= idx (interp-st-full-scratch-len interp-st))
  :measure (nfix n)
  :returns (maybe-index acl2::maybe-natp :rule-classes :type-prescription)
  :guard-hints (("goal" :in-theory (enable stack$a-nth-scratch-kind
                                           stack$a-nth-scratch)))
  (b* ((next (interp-st-scan-for-fnsym idx fn interp-st))
       ((unless next) nil)
       ((when (zp n)) next))
    (interp-st-scan-for-nth-fnsym-occ (1+ next) (1- n) fn interp-st))
  ///
  (defret <fn>-bound
    (implies maybe-index
             (< maybe-index (interp-st-full-scratch-len interp-st)))
    :rule-classes :linear))

(define interp-st-scan-for-next-scratch-fnsym ((n natp) interp-st)
  :guard (<= n (interp-st-full-scratch-len interp-st))
  :measure (nfix (- (interp-st-full-scratch-len interp-st) (nfix n)))
  :returns (maybe-idx acl2::maybe-natp :rule-classes :type-prescription)
  (if (mbe :logic (zp (- (interp-st-full-scratch-len interp-st) (nfix n)))
           :exec (eql n (interp-st-full-scratch-len interp-st)))
      nil
    (if (eq (interp-st-nth-scratch-kind n interp-st) :fnsym)
        (lnfix n)
      (interp-st-scan-for-next-scratch-fnsym (1+ (lnfix n)) interp-st)))
  ///
  (defret <fn>-in-bounds
    (implies maybe-idx
             (< maybe-idx (stack$a-full-scratch-len (interp-st->stack interp-st))))
    :rule-classes :linear)

  (defret <fn>-incr
    (implies maybe-idx
             (<= (nfix n) maybe-idx))
    :rule-classes :linear)

  (defret scratchobj-kind-of-<fn>
    (implies maybe-idx
             (equal (scratchobj-kind
                     (major-stack-nth-scratch maybe-idx (interp-st->stack interp-st)))
                    :fnsym))
    :hints(("Goal" :in-theory (enable stack$a-nth-scratch-kind)))))

(define interp-st-find-next-scratch-fnsym ((n natp) interp-st)
  :guard (<= n (interp-st-full-scratch-len interp-st))
  :returns (fn (pseudo-fnsym-p fn))
  :guard-hints (("goal" :in-theory (enable stack$a-nth-scratch-kind
                                           stack$a-nth-scratch)))
  (let ((idx (interp-st-scan-for-next-scratch-fnsym n interp-st)))
    (and idx
         (interp-st-nth-scratch-fnsym idx interp-st))))

(define interp-st-scan-for-next-non-ignored-scratch-fnsym ((n natp)
                                                           (ignore-fns cmr::pseudo-fnsymlist-p)
                                                           interp-st)
  :guard (<= n (interp-st-full-scratch-len interp-st))
  :measure (nfix (- (interp-st-full-scratch-len interp-st) (nfix n)))
  :returns (maybe-idx acl2::maybe-natp :rule-classes :type-prescription)
  :guard-hints (("goal" :in-theory (enable stack$a-nth-scratch-kind
                                           stack$a-nth-scratch)))
  (b* (((when (mbe :logic (zp (- (interp-st-full-scratch-len interp-st) (nfix n)))
                   :exec (eql n (interp-st-full-scratch-len interp-st))))
        nil)
       (next-idx (interp-st-scan-for-next-scratch-fnsym n interp-st))
       ((unless next-idx) nil)
       (fnsym (interp-st-nth-scratch-fnsym next-idx interp-st))
       ((unless (member-eq fnsym (cmr::pseudo-fnsymlist-fix ignore-fns)))
        next-idx))
    (interp-st-scan-for-next-non-ignored-scratch-fnsym (1+ next-idx) ignore-fns interp-st))
  ///
  (defret <fn>-in-bounds
    (implies maybe-idx
             (< maybe-idx (stack$a-full-scratch-len (interp-st->stack interp-st))))
    :rule-classes :linear)

  (defret <fn>-incr
    (implies maybe-idx
             (<= (nfix n) maybe-idx))
    :rule-classes :linear)

  (defret scratchobj-kind-of-<fn>
    (implies maybe-idx
             (equal (scratchobj-kind
                     (major-stack-nth-scratch maybe-idx (interp-st->stack interp-st)))
                    :fnsym))
    :hints(("Goal" :in-theory (enable stack$a-nth-scratch-kind))))

  (defret non-ignored-of-<fn>
    (implies maybe-idx
             (not (member-equal (scratchobj-fnsym->val
                                 (major-stack-nth-scratch maybe-idx (interp-st->stack interp-st)))
                                (cmr::pseudo-fnsymlist-fix ignore-fns))))
    :hints(("Goal" :in-theory (enable stack$a-nth-scratch-kind
                                      stack$a-nth-scratch)))))
  

(define interp-st-fn-annotation ((fn pseudo-fnsym-p)
                                 (ignore-fns cmr::pseudo-fnsymlist-p)
                                 interp-st)
  :parents (bind-fn-annotation annotate)
  :short "Finds the annotation, if any, of the innermost nesting of fn on the stack."
  :returns (annotation fgl-object-p)
  :guard-hints (("goal" :in-theory (enable stack$a-nth-scratch-kind
                                           stack$a-nth-scratch)))
  (b* ((idx (interp-st-scan-for-fnsym 0 fn interp-st))
       ((unless idx) nil)
       (annot-idx (interp-st-scan-for-next-non-ignored-scratch-fnsym
                   (1+ idx) ignore-fns interp-st)))
    (and annot-idx
         (< (+ 1 idx) annot-idx)
         (eq (interp-st-nth-scratch-fnsym annot-idx interp-st) 'annotate)
         (eq (interp-st-nth-scratch-kind (1- annot-idx) interp-st) :fgl-obj)
         (interp-st-nth-scratch-fgl-obj (1- annot-idx) interp-st))))

(define interp-st-nth-fn-annotation ((n natp)
                                     (fn pseudo-fnsym-p)
                                     (ignore-fns cmr::pseudo-fnsymlist-p)
                                     interp-st)
  :parents (annotate)
  :short "Finds the annotation, if any, of the nth-innermost nesting of fn on the stack."
  :returns (annotation fgl-object-p)
  :guard-hints (("goal" :in-theory (enable stack$a-nth-scratch-kind
                                           stack$a-nth-scratch)))
  (b* ((idx (interp-st-scan-for-nth-fnsym-occ 0 n fn interp-st))
       ((unless idx) nil)
       (annot-idx (interp-st-scan-for-next-non-ignored-scratch-fnsym
                   (1+ idx) ignore-fns interp-st)))
    (and annot-idx
         (< (+ 1 idx) annot-idx)
         (eq (interp-st-nth-scratch-fnsym annot-idx interp-st) 'annotate)
         (eq (interp-st-nth-scratch-kind (1- annot-idx) interp-st) :fgl-obj)
         (interp-st-nth-scratch-fgl-obj (1- annot-idx) interp-st))))

(fancy-ev-add-primitive interp-st-fn-annotation (and (acl2::pseudo-fnsym-p fn)
                                                     (cmr::pseudo-fnsymlist-p ignore-fns)))
(fancy-ev-add-primitive interp-st-nth-fn-annotation (and (natp n)
                                                         (acl2::pseudo-fnsym-p fn)
                                                         (cmr::pseudo-fnsymlist-p ignore-fns)))
(fancy-ev-add-primitive interp-st-find-next-scratch-fnsym
                        (and (natp n) (<= n (interp-st-full-scratch-len interp-st))))
(fancy-ev-add-primitive interp-st-scan-for-fnsym
                        (and (natp n) (pseudo-fnsym-p fn)
                             (<= n (interp-st-full-scratch-len interp-st))))
(fancy-ev-add-primitive interp-st-scan-for-nth-fnsym-occ
                        (and (natp idx) (natp n) (pseudo-fnsym-p fn)
                             (<= idx (interp-st-full-scratch-len interp-st))))

(fancy-ev-add-primitive interp-st-debug-stack
                        (and (natp count) (natp n)
                             (<= n (interp-st-full-scratch-len interp-st))))

(defmacro bind-fn-annotation (varname fn &key ignore-fns)
  `(fgl-prog2 (bind-var ,varname (syntax-interp (interp-st-fn-annotation
                                                 ,fn ,ignore-fns 'interp-st))) t))

(defmacro bind-nth-fn-annotation (varname n fn &key ignore-fns)
  `(fgl-prog2 (bind-var ,varname (syntax-interp (interp-st-nth-fn-annotation
                                                 ,n ,fn ,ignore-fns 'interp-st))) t))

(defxdoc bind-fn-annotation
  :parents (annotate)
  :short "Get the annotation associated with the innermost call of the given function being rewritten"
  :long "<p>See @(see annotate) for an overview of this FGL feature.</p>

<p>Usage:</p>

@({
 (bind-fn-annotation free-var 'my-fn)
 })

<p>finds the record of the innermost call of @('my-fn') in the FGL rewriter's
stack, and checks whether there was a call of @(see annotate) wrapped
immediately around it. If so, it binds the given free variable to the first
argument of that call of annotate; otherwise, it binds it to NIL. The
@('bind-fn-annotation') form always returns T, so it can be used as a
hypothesis in a rewrite rule.</p>

@({
 (bind-fn-annotation free-var 'my-fn :ignore-fns '(bool-fix$inline))
 })

<p>additionally allows calls of @('bool-fix') to occur outside the call of
@('my-fn') and inside the call of @('annotate'). That is, it binds the argument
to the call of @('annotate') if there is one wrapped immediately around
some (optional) calls of @('bool-fix'), wrapped immediately around the
innermost call of @('my-fn').</p>

<p>A related utility is @(see bind-nth-fn-annotation) which gets the annotation
associated with the nth-innermost call of the function, rather than the
innermost.</p>")

(defxdoc bind-nth-fn-annotation
  :parents (annotate)
  :short "Get the annotation associated with the nth-innermost call of the given function being rewritten"
  :long "<p>See @(see annotate) for an overview of this FGL feature.</p>

<p>Usage:</p>

@({
 (bind-nth-fn-annotation free-var 3 'my-fn)
 })

<p>finds the record of the 3rd-innermost call of @('my-fn') in the FGL rewriter's
stack, and binds free-var to its annotation, or NIL if none.</p>

@({
 (bind-nth-fn-annotation free-var 3 'my-fn :ignore-fns '(foo bar))
 })

<p>additionally allows optional intervening calls of @('foo') and @('bar')
between the @('annotate') and @('my-fn') calls.</p>


<p>See also @(see bind-fn-annotation).</p>")
