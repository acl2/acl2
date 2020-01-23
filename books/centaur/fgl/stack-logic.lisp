; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "FGL")

(include-book "fgl-object")
(include-book "rule-types")
(include-book "constraint-inst")

(local (include-book "scratchobj"))

(local (std::add-default-post-define-hook :fix))

(defxdoc fgl-stack
  :parents (fgl)
  :short "Representation of the FGL interpreter stack."
  :long "

<p>FGL stores the stack of its interpreter as a nested stobj @('stack') inside
its @('interp-st') stobj.  But the stack may also be extracted as an ordinary
ACL2 object of type @(see major-stack).  This topic offers an overview of how
these work; specifics of each datatype are in their respective topics.</p>

<p>A @(see major-stack) is a nonempty list of @(see major-frame) objects.  Each
such frame represents an entirely new scope for variables such as a function
definition or rewrite rule application.  Each major-frame contains some
debugging info, a variable bindings alist, and a @(see minor-stack), which is a
nonempty list of @(see minor-frame) objects.  Each minor frame represents a
lambda body within the larger context of the major frame.  It has its own
bindings and debugging info, as well as a list of scratch objects representing
arguments to be passed to subsequent function calls.</p>

<p>The distinction between major and minor stack frames is subtle, especially
given ACL2's insistence that lambdas bind all the variables found in their
bodies.  The difference is that in FGL, when we encounter a lambda nesting, we
preprocess it so as to ignore variables that are re-bound to themselves,
instead keeping the current bindings and only adding to them.  On the other
hand, when we apply a rewrite rule we enter a completely new namespace where
initially only the variables of the unifying substitution are bound.  This lazy
binding of lambdas allows us to support @(see syntax-bind) by allowing us to
leave variables unbound until they are used in a nontrivial way: that is,
passed into a function or bound to a different variable in a lambda.</p>

")

;; This book defines a stack containing "major frames", each containing a stack
;; of "minor frames".  Each major and minor frame contains a binding alist and
;; perhaps some debug info.  The complete set of bindings at a given point in
;; symbolic execution is the local minor frame bindings appended to the local
;; major frame bindings.  Each minor frame also contains a scratch
;; stack, which is a stack of objects of various types.

;; This two-dimensional nesting approach supports the style of symbolic
;; execution we do in GL, specifically late binding of free variables in hyps
;; and RHSes of rules (used for an extension of syntaxp/bind-free).

;; Major stack frames correspond to places in symbolic execution where we enter
;; an entirely new namespace, such as when we enter the body of a function or
;; begin relieving the hyps/executing the RHS of a rewrite rule under the
;; unification substitution.

;; Minor stack frames correspond essentially to entries into lambda bodies.
;; Except, we process nestings of lambdas into bindinglists (see
;; centaur/meta/bindinglist) so that if a lambda call is nested directly inside
;; a lambda body, we reuse the outer frame.  In classical ACL2, each lambda
;; binds all the variables that are used in its body and so a lambda body is in
;; its very own namespace.  However, when we process lambdas into bindinglists,
;; we throw out variables that are bound to themselves, and compensate by
;; appending the new bindings to the existing bindings.  This helps to support
;; late bindings by allowing us to leave variables unbound until they are
;; "really used", that is, passed into a function or bound to a different
;; variable in a lambda.

;; A stack has one or more major stack frames.  A major stack frame has a base
;; binding list, a debug area, and one or more minor stack frames.  A minor
;; stack frame has a binding list, two scratch lists: one for fgl-objects and
;; one for BFRs, and a debug area.

;; See stack.lisp for the stobj implementation of the stack.



(make-event
 `(progn
    (fty::deftagsum scratchobj
      :layout :tree
      :parents (fgl-stack)
      :short "Type of an object stored in an FGL minor stack frame's scratch list."
      . ,(acl2::template-proj '(:<kind> ((val <pred> . <ruleclass>)))
                              *scratchobj-tmplsubsts*))

    (defenum scratchobj-kind-p ,(acl2::template-proj :<kind> *scratchobj-tmplsubsts*))

    (defthm scratchobj-kind-p-of-scratchobj-kind
      (scratchobj-kind-p (scratchobj-kind x))
      :hints(("Goal" :in-theory (enable scratchobj-kind))))))

(make-event
 `(progn
    (define scratchobj-kind->code ((x scratchobj-kind-p))
      :returns (code natp :rule-classes :type-prescription)
      (case x
        ,@(acl2::template-proj '(:<kindcase> <code>) *scratchobj-tmplsubsts*))
      ///
      (local (in-theory (enable scratchobj-kind-fix)))

      (defret unsigned-byte-p-of-<fn>
        (unsigned-byte-p 4 code)))

    (define scratchobj-code->kind ((x natp))
      :returns (kind scratchobj-kind-p)
      (case (lnfix x)
        ,@(acl2::template-proj '(<codecase> :<kind>) *scratchobj-tmplsubsts*))
      ///
      (defthm scratchobj-code->kind-of-scratchobj-kind->code
        (equal (scratchobj-code->kind (scratchobj-kind->code kind))
               (scratchobj-kind-fix kind))
        :hints(("Goal" :in-theory (enable scratchobj-kind->code scratchobj-kind-fix)))))))



(fty::deflist scratchlist :elt-type scratchobj :true-listp t
  :parents (fgl-stack)
  :short "A list of scratch objects (type @(see scratchobj)) representing arguments
          to future function calls, etc.")

(fty::defoption maybe-fgl-generic-rule fgl-generic-rule-p)


(fty::defprod minor-frame
  :parents (fgl-stack)
  :short "A minor stack frame representing a lambda body scope."
  ((bindings fgl-object-bindings-p "The full list of bindings for locally bound variables.")
   (scratch scratchlist-p "The current scratch list.")
   (term pseudo-termp
               "Debug info identifying the lambda call from which this frame arose,
                nil if top level of the current rule")
   (term-index acl2::maybe-natp "Depth-first index of the term we're currently looking at within
                     debug-term"
               :rule-classes :type-prescription)))

(fty::deflist minor-stack :elt-type minor-frame :true-listp t :non-emptyp t
  :parents (fgl-stack)
  :short "A minor stack representing some nesting of lambda scopes within a major stack frame."
  :long "<p>Representation: a nonempty list of frames of type @(see minor-frame).</p>"
  ///
  (defthm minor-stack-p-of-cons-cdr
    (implies (and (minor-stack-p x)
                  (minor-frame-p a))
             (minor-stack-p (cons a (cdr x))))
    :hints(("Goal" :in-theory (enable minor-stack-p)))))

(make-event
 `(fty::defprod major-frame
    :parents (fgl-stack)
    :short "A major stack frame representing an entirely new namespace such as
            a function definition or rewrite rule."
    ((bindings fgl-object-bindings-p "Top-level variable bindings of the scope.")
     (rule maybe-fgl-generic-rule-p "Rule applied to make this stack frame.")
     (phase acl2::maybe-natp :rule-classes :type-prescription
            "Hyp number or RHS when greater")
     (minor-stack minor-stack-p :default ',(list (make-minor-frame))
                  "The minor stack representing the current nesting of lambdas within the scope."))))

(fty::deflist major-stack :elt-type major-frame :true-listp t :non-emptyp t
  :parents (fgl-stack)
  :short "A stack representing the current nesting of rule applications."
  :long "<p>Representation: a nonempty list of frames of type @(see major-frame).</p>"
  ///
  (defthm major-stack-p-of-cons-cdr
    (implies (and (major-stack-p x)
                  (major-frame-p a))
             (major-stack-p (cons a (cdr x))))
    :hints(("Goal" :in-theory (enable major-stack-p)))))




(define stack$a-frames ((x major-stack-p))
  :returns (nframes posp :rule-classes :type-prescription)
  (len (major-stack-fix x)))

(define stack$a-push-frame ((x major-stack-p))
  :returns (stack major-stack-p)
  (cons (make-major-frame) (major-stack-fix x)))


(local (defthm major-frame-p-of-nth
         (implies (and (major-stack-p x)
                       (< (nfix n) (len x)))
                  (major-frame-p (nth n x)))
         :hints(("Goal" :in-theory (enable nth major-stack-p len)))))

(local (defthm len-when-major-stack-p
         (implies (major-stack-p x)
                  (< 0 (len x)))
         :hints(("Goal" :in-theory (enable major-stack-p len)))
         :rule-classes :linear))

(local (defthm minor-frame-p-of-nth
         (implies (and (minor-stack-p x)
                       (< (nfix n) (len x)))
                  (minor-frame-p (nth n x)))
         :hints(("Goal" :in-theory (enable nth minor-stack-p len)))))

(local (defthm len-when-minor-stack-p
         (implies (minor-stack-p x)
                  (< 0 (len x)))
         :hints(("Goal" :in-theory (enable minor-stack-p len)))
         :rule-classes :linear))

(define stack$a-minor-frames ((x major-stack-p))
  :returns (nframes posp :rule-classes :type-prescription)
  (len (major-frame->minor-stack (car x))))

(define stack$a-nth-frame-minor-frames ((n natp)
                                        (x major-stack-p))
  :guard (< n (stack$a-frames x))
  :guard-hints (("goal" :in-theory (enable stack$a-frames max)))
  :returns (nframes posp :rule-classes :type-prescription)
  (len (major-frame->minor-stack (nth (mbe :logic (min (nfix n) (1- (stack$a-frames x)))
                                           :exec n)
                                      (major-stack-fix x)))))

(define stack$a-push-minor-frame ((x major-stack-p))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x)))
    (major-stack-fix
     (cons (change-major-frame jframe :minor-stack
                               (cons (make-minor-frame) jframe.minor-stack))
           (cdr x)))))

(define stack$a-set-bindings ((bindings fgl-object-bindings-p)
                              (x major-stack-p))
  :returns (stack major-stack-p)  
  (major-stack-fix (cons (change-major-frame (car x) :bindings bindings)
                         (cdr x))))

(define stack$a-add-binding ((var pseudo-var-p)
                             (val fgl-object-p)
                             (x major-stack-p))
  :returns (stack major-stack-p)
  (b* (((major-frame frame) (car x)))
    (major-stack-fix (cons (change-major-frame frame :bindings (cons (cons (pseudo-var-fix var)
                                                                           (fgl-object-fix val))
                                                                     frame.bindings))
                           (cdr x)))))

(define stack$a-set-rule ((rule maybe-fgl-generic-rule-p)
                          (x major-stack-p))
  :returns (stack major-stack-p)
  (major-stack-fix (cons (change-major-frame (car x) :rule rule)
                         (cdr x))))

(define stack$a-set-phase ((phase acl2::maybe-natp)
                           (x major-stack-p))
  :returns (stack major-stack-p)
  (major-stack-fix (cons (change-major-frame (car x) :phase phase)
                         (cdr x))))


(local (defthm fgl-object-bindings-p-of-append
           (implies (and (fgl-object-bindings-p x)
                         (fgl-object-bindings-p y))
                    (fgl-object-bindings-p (append x y)))))

(define stack$a-set-minor-bindings ((bindings fgl-object-bindings-p)
                                    (x major-stack-p))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x))
       (nframe (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe :bindings bindings)
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(define stack$a-add-minor-bindings ((bindings fgl-object-bindings-p)
                                    (x major-stack-p))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe
                                                                         :bindings (append bindings nframe.bindings))
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))


(define stack$a-set-term ((term pseudo-termp)
                          (x major-stack-p))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x))
       (nframe (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe :term term)
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(define stack$a-set-term-index ((term-index acl2::maybe-natp)
                                (x major-stack-p))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x))
       (nframe (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe :term-index term-index)
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(define stack$a-bindings ((x major-stack-p))
  :returns (bindings fgl-object-bindings-p)
  (major-frame->bindings (car x)))

                  

(define stack$a-nth-frame-bindings ((n natp)
                                    (x major-stack-p))
  :guard (< n (stack$a-frames x))
  :guard-hints (("goal" :in-theory (enable stack$a-frames max)))
  :returns (bindings fgl-object-bindings-p)
  (major-frame->bindings (nth (mbe :logic (min (1- (stack$a-frames x)) (nfix n))
                                   :exec n)
                              (major-stack-fix x))))


(define stack$a-minor-bindings ((x major-stack-p))
  :returns (binings fgl-object-bindings-p)
  (minor-frame->bindings (car (major-frame->minor-stack (car x)))))

(define stack$a-nth-frame-minor-bindings ((n natp)
                                          (m natp)
                                          (x major-stack-p))
  :guard (and (< n (stack$a-frames x))
              (< m (stack$a-nth-frame-minor-frames n x)))
  :guard-hints (("goal" :in-theory (enable stack$a-frames stack$a-nth-frame-minor-frames
                                           max)))
  :returns (bindings fgl-object-bindings-p)
  (minor-frame->bindings
   (nth (mbe :logic (min (1- (stack$a-nth-frame-minor-frames n x)) (nfix m))
             :exec m)
        (major-frame->minor-stack (nth (mbe :logic (min (nfix n) (1- (stack$a-frames x)))
                                            :exec n)
                                       (major-stack-fix x))))))




(define stack$a-rule ((x major-stack-p))
  :returns (rule maybe-fgl-generic-rule-p)
  (major-frame->rule (car x)))

(define stack$a-phase ((x major-stack-p))
  :returns (phase acl2::maybe-natp :rule-classes :type-prescription)
  (major-frame->phase (car x)))


(define stack$a-term ((x major-stack-p))
  :returns (term pseudo-termp)
  (minor-frame->term (car (major-frame->minor-stack (car x)))))

(define stack$a-term-index ((x major-stack-p))
  :returns (term-index acl2::maybe-natp :rule-classes :type-prescription)
  (minor-frame->term-index (car (major-frame->minor-stack (car x)))))


(define stack$a-scratch-len ((x major-stack-p))
  (len (minor-frame->scratch (car (major-frame->minor-stack (car x))))))


(define stack$a-top-scratch ((x major-stack-p))
  :guard (< 0 (stack$a-scratch-len x))
  :guard-hints (("goal" :in-theory (enable stack$a-scratch-len)))
  :returns (obj scratchobj-p)
  (scratchobj-fix (car (minor-frame->scratch (car (major-frame->minor-stack (car x)))))))




(define minor-stack-scratch-len ((x minor-stack-p))
  :ruler-extenders (binary-+)
  :returns (len natp :rule-classes :type-prescription)
  (+ (len (minor-frame->scratch (car x)))
     (if (consp (cdr x))
         (minor-stack-scratch-len (cdr x))
       0)))

(define major-stack-scratch-len ((x major-stack-p))
  :ruler-extenders (binary-+)
  :returns (len natp :rule-classes :type-prescription)
  (+ (minor-stack-scratch-len (major-frame->minor-stack (car x)))
     (if (consp (cdr x))
         (major-stack-scratch-len (cdr x))
       0)))

(define stack$a-full-scratch-len ((x major-stack-p))
  (major-stack-scratch-len x))

(define minor-stack-nth-scratch ((n natp) (x minor-stack-p))
  :guard (< n (minor-stack-scratch-len x))
  :prepwork ((local (in-theory (enable minor-stack-scratch-len))))
  :measure (len x)
  :returns (obj scratchobj-p)
  (b* ((scratch (minor-frame->scratch (car x)))
       (len (len scratch)))
    (if (< (lnfix n) len)
        (scratchobj-fix (nth n scratch))
      (if (mbt (consp (cdr x)))
          (minor-stack-nth-scratch (- (lnfix n) len) (cdr x))
        (scratchobj-fix nil)))))

(define major-stack-nth-scratch ((n natp) (x major-stack-p))
  :guard (< n (major-stack-scratch-len x))
  :prepwork ((local (in-theory (enable major-stack-scratch-len))))
  :measure (len x)
  :returns (obj scratchobj-p)
  (b* ((minor-stack (major-frame->minor-stack (car x)))
       (len (minor-stack-scratch-len minor-stack)))
    (if (mbe :logic (or (< (lnfix n) len) (atom (cdr x)))
             :exec (< (lnfix n) len))
        (minor-stack-nth-scratch n minor-stack)
      (major-stack-nth-scratch (- (lnfix n) len) (cdr x)))))

(define stack$a-nth-scratch ((n natp)
                             (x major-stack-p))
  :guard (< n (stack$a-full-scratch-len x))
  :guard-hints (("goal" :in-theory (enable stack$a-full-scratch-len)))
  :returns (obj scratchobj-p)
  (major-stack-nth-scratch n x))

(define stack$a-nth-scratch-kind ((n natp)
                                  (x major-stack-p))
  :guard (< n (stack$a-full-scratch-len x))
  :guard-hints (("goal" :in-theory (enable stack$a-full-scratch-len)))
  (scratchobj-kind (major-stack-nth-scratch n x)))




(define stack$a-pop-scratch ((x major-stack-p))
  :guard (< 0 (stack$a-scratch-len x))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe
                                                                         :scratch
                                                                         (cdr nframe.scratch))
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(define stack$a-pop-multi-scratch ((n natp)
                                   (x major-stack-p))
  :guard (< n (stack$a-scratch-len x))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe
                                                                         :scratch
                                                                         (nthcdr n nframe.scratch))
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))


(define stack$a-push-scratch ((obj scratchobj-p)
                              (x major-stack-p))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack))) 
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe
                                                                         :scratch (cons
                                                                                   obj
                                                                                   nframe.scratch))
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(fty::deffixcong scratchobj-equiv scratchlist-equiv (update-nth n v x) v)

(define stack$a-update-scratch ((n natp)
                                (obj scratchobj-p)
                                (x major-stack-p))
  :returns (stack major-stack-p)
  :guard (< n (stack$a-scratch-len x))
  :guard-hints (("goal" :in-theory (enable stack$a-scratch-len)))
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack))) 
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe
                                                                         :scratch (update-nth n
                                                                                              obj
                                                                                              nframe.scratch))
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))


(local
 (progn
   (defconst *scratchobj-template*
     '(progn (define stack$a-push-scratch-<kind> ((obj <pred>)
                                                  (x major-stack-p))
               :returns (stack major-stack-p)
               :enabled t
               (stack$a-push-scratch (scratchobj-<kind> obj) x))

             (define stack$a-top-scratch-<kind> ((x major-stack-p))
               :guard (and (< 0 (stack$a-scratch-len x))
                           (scratchobj-case (stack$a-top-scratch x) :<kind>))
               :guard-hints (("goal" :in-theory (enable stack$a-scratch-len
                                                        stack$a-top-scratch)))
               :returns (obj <pred>)
               :enabled t
               (scratchobj-<kind>->val (stack$a-top-scratch x)))

             (define stack$a-nth-scratch-<kind> ((n natp)
                                                 (x major-stack-p))
               :guard (and (< n (stack$a-full-scratch-len x))
                           (scratchobj-case (stack$a-nth-scratch n x) :<kind>))
               :guard-hints (("goal" :in-theory (enable stack$a-full-scratch-len
                                                        stack$a-nth-scratch)))
               :returns (obj <pred>)
               :enabled t
               (scratchobj-<kind>->val (stack$a-nth-scratch n x)))

             (define stack$a-update-scratch-<kind> ((n natp)
                                                    (obj <pred>)
                                                    (x major-stack-p))
               :guard (< n (stack$a-scratch-len x))
               :guard-hints (("goal" :in-theory (enable stack$a-scratch-len
                                                        stack$a-nth-scratch)))
               :returns (stack major-stack-p)
               :enabled t
               (stack$a-update-scratch n (scratchobj-<kind> obj) x))

             (define stack$a-pop-scratch-<kind> ((x major-stack-p))
               :guard (and (< 0 (stack$a-scratch-len x))
                           (scratchobj-case (stack$a-top-scratch x) :<kind>))
               :guard-hints (("goal" :in-theory (enable stack$a-scratch-len
                                                        stack$a-top-scratch)))
               :enabled t
               (mv (stack$a-top-scratch-<kind> x)
                   (stack$a-pop-scratch x)))))))

(make-event
 (cons 'progn (acl2::template-proj *scratchobj-template*
                                   *scratchobj-tmplsubsts*)))









(local (defthm len-gt-0
         (equal (< 0 (len x))
                (consp x))))

(local (defthm <-cancel
         (implies (syntaxp (and (quotep c1) (quotep c2)))
                  (equal (< c1 (+ c2 x))
                         (< (- c1 c2) (fix x))))
         :hints (("goal" :Cases ((< c1 (+ c2 x)))))))

(define stack$a-pop-minor-frame ((x major-stack-p))
  :guard (and (< 1 (stack$a-minor-frames x))
              (eql (stack$a-scratch-len x) 0))
  :guard-hints (("goal" :in-theory (enable stack$a-minor-frames)))
  :returns (stack major-stack-p)
  (b* (((major-frame jframe) (car x)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack (cdr jframe.minor-stack))
                           (cdr x)))))

(define stack$a-pop-frame ((x major-stack-p))
  :guard (and (< 1 (stack$a-frames x))
              (eql 1 (stack$a-minor-frames x))
              (eql 0 (stack$a-scratch-len x)))
  :guard-hints (("goal" :in-theory (enable stack$a-frames)))
  :returns (stack major-stack-p)
  (major-stack-fix (cdr x)))

(define stack$a-extract ((x major-stack-p))
  :enabled t
  (major-stack-fix x))





(define create-stack$a ()
  :enabled t
  :returns (stack major-stack-p)
  (list (make-major-frame)))


(define stack$a-empty ((x major-stack-p))
  (declare (ignore x))
  :enabled t
  (list (make-major-frame)))








;; BOZO Unfortunately scratchobj-bfrlist is the constructor for the bfrlist
;; kind of scratchobj so we use an unconventional name.
(define scratchobj->bfrlist ((x scratchobj-p))
  :returns (bfrs)
  (scratchobj-case x
    :fgl-obj (fgl-object-bfrlist x.val)
    :fgl-objlist (fgl-objectlist-bfrlist x.val)
    :bfr (list x.val)
    :bfrlist x.val
    :cinst (constraint-instance-bfrlist x.val)
    :cinstlist (constraint-instancelist-bfrlist x.val))
  ///
  (local (include-book "scratchobj"))
  (make-event
   `(defthm scratchobj->bfrlist-of-make-scratchobjs
      (and ,@(acl2::template-proj
              '(equal (scratchobj->bfrlist (scratchobj-<kind> x))
                      (<prefix>-bfrlist x))
              (scratchobj-tmplsubsts (acl2::remove-assoc
                                      :bfr (acl2::remove-assoc :bfrlist *scratchobj-types*))))
           (equal (scratchobj->bfrlist (scratchobj-bfr x)) (list x))
           (equal (scratchobj->bfrlist (scratchobj-bfrlist x)) (true-list-fix x)))))

  (deffixequiv scratchobj->bfrlist)

  (make-event
   (cons 'progn
         (acl2::template-proj
          '(defthm bfrlist-of-scratchobj-<kind>->val
             (implies (scratchobj-case x :<kind>)
                      (equal (<prefix>-bfrlist (scratchobj-<kind>->val x))
                             (scratchobj->bfrlist x))))
          (scratchobj-tmplsubsts (acl2::remove-assoc
                                  :bfr (acl2::remove-assoc :bfrlist *scratchobj-types*))))))

  (defthm bfrlist-of-scratchobj-bfr->val
    (implies (and (not (member v (scratchobj->bfrlist x)))
                  (scratchobj-case x :bfr))
             (not (equal v (scratchobj-bfr->val x)))))

  (defthm bfrlist-of-scratchobj-bfrlist->val
    (implies (and (not (member v (scratchobj->bfrlist x)))
                  (scratchobj-case x :bfrlist))
             (not (member v (scratchobj-bfrlist->val x))))))

  

(define scratchlist-bfrlist ((x scratchlist-p))
  :returns (bfrs)
  (if (atom x)
      nil
    (append (scratchobj->bfrlist (car x))
            (scratchlist-bfrlist (cdr x))))
  ///
  (defthm scratchlist-bfrlist-of-cons
    (equal (scratchlist-bfrlist (cons a b))
           (append (scratchobj->bfrlist a)
                   (scratchlist-bfrlist b))))

  (defthm scratchobj->bfrlist-of-car
    (implies (not (member v (scratchlist-bfrlist x)))
             (not (member v (scratchobj->bfrlist (car x))))))

  (defthm scratchlist-bfrlist-of-car
    (implies (not (member v (scratchlist-bfrlist x)))
             (not (member v (scratchlist-bfrlist (cdr x)))))))

(define minor-frame-bfrlist ((x minor-frame-p))
  :returns (bfrs)
  (b* (((minor-frame x)))
    (append (fgl-object-bindings-bfrlist x.bindings)
            (scratchlist-bfrlist x.scratch)))
  ///
  (defthm minor-frame-bfrlist-of-minor-frame
    (equal (minor-frame-bfrlist (minor-frame bindings scratch term term-index))
           (append (fgl-object-bindings-bfrlist bindings)
                   (scratchlist-bfrlist scratch))))

  (defthm bfrlist-of-minor-frame->bindings
    (implies (not (member v (minor-frame-bfrlist x)))
             (not (member v (fgl-object-bindings-bfrlist (minor-frame->bindings x))))))

  (defthm bfrlist-of-minor-frame->scratch
    (implies (not (member v (minor-frame-bfrlist x)))
             (not (member v (scratchlist-bfrlist (minor-frame->scratch x)))))))

(define minor-stack-bfrlist ((x minor-stack-p))
  :returns (bfrs)
  :ruler-extenders (binary-append)
  (append (minor-frame-bfrlist (car x))
          (and (consp (cdr x))
               (minor-stack-bfrlist (cdr x))))
  ///
  (defthm minor-stack-bfrlist-of-cons
    (equal (minor-stack-bfrlist (cons a b))
           (append (minor-frame-bfrlist a)
                   (minor-stack-bfrlist b))))

  (defthm minor-frame-bfrlist-of-car
    (implies (not (member v (minor-stack-bfrlist x)))
             (not (member v (minor-frame-bfrlist (car x))))))

  (defthm minor-stack-bfrlist-of-car
    (implies (not (member v (minor-stack-bfrlist x)))
             (not (member v (minor-stack-bfrlist (cdr x)))))))

(define major-frame-bfrlist ((x major-frame-p))
  :returns (bfrs)
  (b* (((major-frame x)))
    (append (fgl-object-bindings-bfrlist x.bindings)
            (minor-stack-bfrlist x.minor-stack)))
  ///
  (defthm major-frame-bfrlist-of-major-frame
    (equal (major-frame-bfrlist (major-frame bindings rule phase minor-stack))
           (append (fgl-object-bindings-bfrlist bindings)
                   (minor-stack-bfrlist minor-stack))))

  (defthm bfrlist-of-major-frame->bindings
    (implies (not (member v (major-frame-bfrlist x)))
             (not (member v (fgl-object-bindings-bfrlist (major-frame->bindings x))))))

  (defthm bfrlist-of-major-frame->minor-stack
    (implies (not (member v (major-frame-bfrlist x)))
             (not (member v (minor-stack-bfrlist (major-frame->minor-stack x)))))))

(define major-stack-bfrlist ((x major-stack-p))
  :returns (bfrs)
  :ruler-extenders (binary-append)
  (append (major-frame-bfrlist (car x))
          (and (consp (cdr x))
               (major-stack-bfrlist (cdr x))))
  ///
  (defthm major-stack-bfrlist-of-cons
    (equal (major-stack-bfrlist (cons a b))
           (append (major-frame-bfrlist a)
                   (major-stack-bfrlist b))))

  (defthm major-frame-bfrlist-of-car
    (implies (not (member v (major-stack-bfrlist x)))
             (not (member v (major-frame-bfrlist (car x))))))

  (defthm major-stack-bfrlist-of-car
    (implies (not (member v (major-stack-bfrlist x)))
             (not (member v (major-stack-bfrlist (cdr x)))))))
