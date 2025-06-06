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
 })"
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

(define interp-st-find-next-scratch-fnsym ((n natp) interp-st)
  :guard (<= n (interp-st-full-scratch-len interp-st))
  :measure (nfix (- (interp-st-full-scratch-len interp-st) (nfix n)))
  :returns (fn (pseudo-fnsym-p fn))
  :guard-hints (("goal" :in-theory (enable stack$a-nth-scratch-kind
                                           stack$a-nth-scratch)))
  (if (mbe :logic (zp (- (interp-st-full-scratch-len interp-st) (nfix n)))
           :exec (eql n (interp-st-full-scratch-len interp-st)))
      nil
    (if (eq (interp-st-nth-scratch-kind n interp-st) :fnsym)
        (interp-st-nth-scratch-fnsym n interp-st)
      (interp-st-find-next-scratch-fnsym (1+ (lnfix n)) interp-st))))

(define interp-st-fn-annotation ((fn pseudo-fnsym-p)
                                 interp-st)
  :short "Finds the annotation, if any, of the innermost nesting of fn on the stack."
  :returns (annotation fgl-object-p)
  :guard-hints (("goal" :in-theory (enable stack$a-nth-scratch-kind
                                           stack$a-nth-scratch)))
  (b* ((idx (interp-st-scan-for-fnsym 0 fn interp-st))
       ((unless idx) nil)
       ((when (<= (- (interp-st-full-scratch-len interp-st) 2) idx))
        nil))
    (and (eq (interp-st-nth-scratch-kind (+ 2 idx) interp-st) :fnsym)
         (eq (interp-st-nth-scratch-fnsym (+ 2 idx) interp-st) 'annotate)
         (eq (interp-st-nth-scratch-kind (+ 1 idx) interp-st) :fgl-obj)
         (interp-st-nth-scratch-fgl-obj (+ 1 idx) interp-st))))

(define interp-st-nth-fn-annotation ((n natp)
                                     (fn pseudo-fnsym-p)
                                     interp-st)
  :parents (annotate)
  :short "Finds the annotation, if any, of the nth-innermost nesting of fn on the stack."
  :returns (annotation fgl-object-p)
  :guard-hints (("goal" :in-theory (enable stack$a-nth-scratch-kind
                                           stack$a-nth-scratch)))
  (b* ((idx (interp-st-scan-for-nth-fnsym-occ 0 n fn interp-st))
       ((unless idx) nil)
       ((when (<= (- (interp-st-full-scratch-len interp-st) 2) idx))
        nil))
    (and (eq (interp-st-nth-scratch-kind (+ 2 idx) interp-st) :fnsym)
         (eq (interp-st-nth-scratch-fnsym (+ 2 idx) interp-st) 'annotate)
         (eq (interp-st-nth-scratch-kind (+ 1 idx) interp-st) :fgl-obj)
         (interp-st-nth-scratch-fgl-obj (+ 1 idx) interp-st))))

(fancy-ev-add-primitive interp-st-fn-annotation (acl2::pseudo-fnsym-p fn))
(fancy-ev-add-primitive interp-st-nth-fn-annotation (and (natp n) (acl2::pseudo-fnsym-p fn)))
(fancy-ev-add-primitive interp-st-find-next-scratch-fnsym
                        (and (natp n) (<= n (interp-st-full-scratch-len interp-st))))
(fancy-ev-add-primitive interp-st-scan-for-fnsym
                        (and (natp n) (pseudo-fnsym-p fn)
                             (<= n (interp-st-full-scratch-len interp-st))))
(fancy-ev-add-primitive interp-st-scan-for-nth-fnsym-occ
                        (and (natp idx) (natp n) (pseudo-fnsym-p fn)
                             (<= idx (interp-st-full-scratch-len interp-st))))


(defmacro bind-fn-annotation (varname fn)
  `(fgl-prog2 (bind-var ,varname (syntax-interp (interp-st-fn-annotation ,fn 'interp-st))) t))

(defmacro bind-nth-fn-annotation (varname n fn)
  `(fgl-prog2 (bind-var ,varname (syntax-interp (interp-st-nth-fn-annotation ,n ,fn 'interp-st))) t))

(defxdoc bind-fn-annotation
  :parents (annotate)
  :short "Get the annotation associated with the innermost call of the given function being rewritten"
  :long "<p>Usage:</p>

@({
 (bind-fn-annotation free-var 'my-fn)
 })

<p>finds the record of the innermost call of @('my-fn') in the FGL rewriter's
stack, and checks whether there was a call of @(see annotate) wrapped
immediately around it. If so, it binds the given free variable to the first
argument of that call of annotate; otherwise, it binds it to NIL. The
@('bind-fn-annotation') form always returns T, so it can be used as a
hypothesis in a rewrite rule.</p>

<p>A related utility is @(see bind-nth-fn-annotation) which gets the annotation
associated with the nth-innermost call of the function, rather than the
innermost.</p>")

(defxdoc bind-nth-fn-annotation
  :parents (annotate)
  :short "Get the annotation associated with the nth-innermost call of the given function being rewritten"
  :long "<p>Usage:</p>

@({
 (bind-fn-annotation free-var 3 'my-fn)
 })

<p>finds the record of the 3rd-innermost call of @('my-fn') in the FGL rewriter's
stack, and binds free-var to its annotation, or NIL if none.</p>

<p>See also @(see bind-fn-annotation).</p>")
