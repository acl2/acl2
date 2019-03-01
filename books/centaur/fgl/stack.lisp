; GL - A Symbolic Simulation Framework for ACL2
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

(include-book "gl-object")
(include-book "std/stobjs/absstobjs" :dir :System)

(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))

(local (include-book "std/util/termhints" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/stobjs/updater-independence" :dir :system))

(local (in-theory (enable* acl2::arith-equiv-forwarding)))

(local (fty::deflist gl-objectlist :elt-type gl-object :true-listp t))

(local (in-theory (disable nth acl2::nth-when-zp update-nth (tau-system))))

(local (std::add-default-post-define-hook :fix))

;; This book defines a stack containing "major frames", each containing a stack
;; of "minor frames".

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
;; binds all the variables that are used in its body.  However, when we process
;; lambdas into bindinglists, we throw out variables that are bound to
;; themselves, and compensate by appending the new bindings to the existing
;; bindings.  This helps to support late bindings by allowing us to leave
;; variables unbound until they are "really used", that is, passed into a
;; function or bound to a different variable in a lambda.

;; A stack has one or more major stack frames.  A major stack frame has a base
;; binding list, a debug area, and one or more minor stack frames.  A minor
;; stack frame has a binding list, two scratch lists: one for gl-objects and
;; one for BFRs, and a debug area.

;; The stobj implementation of the stack has three arrays:
;; - one for minor frames' bindings, scratch, bool-scratch, debug fields interleaved
;; - one for major frames' bindings and debug fields interleaved
;; - one for the top minor frame pointer of each major frame.

;; A major frame's bottommost minor stack frame is frame 0 for major frame 0,
;; and the frame after the previous major frame's topmost minor stack frame for
;; others.

;; The topmost major frame's top minor frame pointer is redundantly recorded in
;; a top-level field for 1-step access.



(fty::defprod minor-frame
  ((bindings gl-object-alist-p)
   (scratch gl-objectlist-p)
   (bool-scratch true-listp :rule-classes :type-prescription)
   (debug)))

(fty::deflist minor-stack :elt-type minor-frame :true-listp t :non-emptyp t
  ///
  (defthm minor-stack-p-of-cons-cdr
    (implies (and (minor-stack-p x)
                  (minor-frame-p a))
             (minor-stack-p (cons a (cdr x))))
    :hints(("Goal" :in-theory (enable minor-stack-p)))))

(make-event
 `(fty::defprod major-frame
    ((bindings gl-object-alist-p)
     (debug)
     (minor-stack minor-stack-p :default ',(list (make-minor-frame))))))

(fty::deflist major-stack :elt-type major-frame :true-listp t :non-emptyp t
  ///
  (defthm major-stack-p-of-cons-cdr
    (implies (and (major-stack-p x)
                  (major-frame-p a))
             (major-stack-p (cons a (cdr x))))
    :hints(("Goal" :in-theory (enable major-stack-p)))))

(define stack$a-frames ((x major-stack-p))
  :enabled t
  (len (major-stack-fix x)))

(define stack$a-push-frame ((x major-stack-p))
  :enabled t
  (cons (make-major-frame) (major-stack-fix x)))

(define stack$a-minor-frames ((x major-stack-p))
  :enabled t
  (len (major-frame->minor-stack (car x))))

(define stack$a-push-minor-frame ((x major-stack-p))
  :enabled t
  (b* (((major-frame jframe) (car x)))
    (major-stack-fix
     (cons (change-major-frame jframe :minor-stack
                               (cons (make-minor-frame) jframe.minor-stack))
           (cdr x)))))

(define stack$a-set-bindings ((bindings gl-object-alist-p)
                              (x major-stack-p))
  :enabled t
  (major-stack-fix (cons (change-major-frame (car x) :bindings bindings)
                         (cdr x))))

(define stack$a-add-binding ((var pseudo-var-p)
                             (val gl-object-p)
                             (x major-stack-p))
  :enabled t
  (b* (((major-frame frame) (car x)))
    (major-stack-fix (cons (change-major-frame frame :bindings (cons (cons (pseudo-var-fix var)
                                                                           (gl-object-fix val))
                                                                     frame.bindings))
                           (cdr x)))))

(define stack$a-set-debug (debug
                           (x major-stack-p))
  :enabled t
  (major-stack-fix (cons (change-major-frame (car x) :debug debug)
                         (cdr x))))


(local (defthm gl-object-alist-p-of-append
           (implies (and (gl-object-alist-p x)
                         (gl-object-alist-p y))
                    (gl-object-alist-p (append x y)))))

(define stack$a-set-minor-bindings ((bindings gl-object-alist-p)
                                    (x major-stack-p))
  :enabled t
  (b* (((major-frame jframe) (car x))
       (nframe (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe :bindings bindings)
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(define stack$a-add-minor-bindings ((bindings gl-object-alist-p)
                                    (x major-stack-p))
  :enabled t
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe
                                                                         :bindings (append bindings nframe.bindings))
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(define stack$a-push-scratch ((obj gl-object-p)
                              (x major-stack-p))
  :enabled t
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe
                                                                         :scratch (cons obj nframe.scratch))
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(define stack$a-push-bool-scratch ((bfr)
                                   (x major-stack-p))
  :enabled t
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame
                            jframe
                            :minor-stack
                            (cons (change-minor-frame nframe
                                                      :bool-scratch (cons bfr nframe.bool-scratch))
                                  (cdr jframe.minor-stack)))
                           (cdr x)))))

(define stack$a-set-minor-debug ((debug)
                                 (x major-stack-p))
  :enabled t
  (b* (((major-frame jframe) (car x))
       (nframe (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe :debug debug)
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(define stack$a-bindings ((x major-stack-p))
  :enabled t
  (major-frame->bindings (car x)))

(define stack$a-minor-bindings ((x major-stack-p))
  :enabled t
  (minor-frame->bindings (car (major-frame->minor-stack (car x)))))

(define stack$a-debug ((x major-stack-p))
  :enabled t
  (major-frame->debug (car x)))

(define stack$a-minor-debug ((x major-stack-p))
  :enabled t
  (minor-frame->debug (car (major-frame->minor-stack (car x)))))

(define stack$a-scratch-len ((x major-stack-p))
  :enabled t
  (len (minor-frame->scratch (car (major-frame->minor-stack (car x))))))


(define stack$a-pop-scratch ((n natp)
                             (x major-stack-p))
  :guard (<= n (stack$a-scratch-len x))
  :enabled t
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe
                                                                         :scratch
                                                                         (nthcdr n nframe.scratch))
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(define stack$a-bool-scratch-len ((x major-stack-p))
  :enabled t
  (len (minor-frame->bool-scratch (car (major-frame->minor-stack (car x))))))


(define stack$a-pop-bool-scratch ((n natp)
                                  (x major-stack-p))
  :guard (<= n (stack$a-scratch-len x))
  :enabled t
  (b* (((major-frame jframe) (car x))
       ((minor-frame nframe) (car jframe.minor-stack)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                               (cons (change-minor-frame nframe
                                                                         :bool-scratch
                                                                         (nthcdr n nframe.bool-scratch))
                                                     (cdr jframe.minor-stack)))
                           (cdr x)))))

(define stack$a-scratch ((x major-stack-p))
  :enabled t
  (minor-frame->scratch (car (major-frame->minor-stack (car x)))))

(define stack$a-bool-scratch ((x major-stack-p))
  :enabled t
  (minor-frame->bool-scratch (car (major-frame->minor-stack (car x)))))

(local (defthm len-gt-0
         (equal (< 0 (len x))
                (consp x))))

(local (defthm <-cancel
         (implies (syntaxp (and (quotep c1) (quotep c2)))
                  (equal (< c1 (+ c2 x))
                         (< (- c1 c2) (fix x))))
         :hints (("goal" :Cases ((< c1 (+ c2 x)))))))

(define stack$a-pop-minor-frame ((x major-stack-p))
  :enabled t
  :guard (< 1 (stack$a-minor-frames x))
  (b* (((major-frame jframe) (car x)))
    (major-stack-fix (cons (change-major-frame jframe :minor-stack (cdr jframe.minor-stack))
                           (cdr x)))))

(define stack$a-pop-frame ((x major-stack-p))
  :enabled t
  :guard (and (< 1 (stack$a-frames x))
              (eql 1 (stack$a-minor-frames x)))
  (major-stack-fix (cdr x)))

(define stack$a-extract ((x major-stack-p))
  :enabled t
  (major-stack-fix x))

(define create-stack$a ()
  :enabled t
  (list (make-major-frame)))

;; (local
;;  (defthm major-frame-p-of-nth-when-major-stack-p
;;    (implies (and (major-stack-p x)
;;                  (< (nfix n) (len x)))
;;             (major-frame-p (nth n x)))
;;    :hints(("Goal" :in-theory (enable major-stack-p nth)))))

;; (local
;;  (defthm minor-frame-p-of-nth-when-minor-stack-p
;;    (implies (and (minor-stack-p x)
;;                  (< (nfix n) (len x)))
;;             (minor-frame-p (nth n x)))
;;    :hints(("Goal" :in-theory (enable minor-stack-p nth)))))

;; (define stack$a-nth-frame ((n natp)
;;                            (x major-stack-p))
;;   ;; for debugging mostly
;;   :enabled t
;;   :guard (< n (stack$a-len x))
;;   (stack-frame-fix (nth n x)))

;; (defthm major-stack-p-of-cdr
;;   (implies (and (major-stack-p x)
;;                 (< 1 (len x)))
;;            (major-stack-p (cdr x)))
;;   :hints(("Goal" :in-theory (enable major-stack-p))))
                  
       
;; (define major-stack-pop-frame ((x major-stack-p))
;;   :enabled t
;;   :guard (< 1 (stack$a-len x))
;;   (major-stack-fix (cdr x)))


(local (defthm nfix-when-natp
         (implies (natp n)
                  (equal (nfix n) n))))

(local (defthm max-greater-equal-1
         (<= a (max a b))
         :rule-classes :linear))
(local (defthm max-greater-equal-2
         (<= b (max a b))
         :rule-classes :linear))
(local (in-theory (disable not max nfix natp len resize-list)))

(local (std::remove-default-post-define-hook :fix))

(defstobj stack$c
  (stack$c-minor :type (array t (4)) :resizable t)
  (stack$c-major :type (array t (2)) :resizable t)
  (stack$c-top-minor :type (array (unsigned-byte 32) (1)) :resizable t :initially 0)
  (stack$c-top-frame :type (unsigned-byte 32) :initially 0)
  (stack$c-top-minor-frame :type (unsigned-byte 32) :initially 0)
  :renaming ((stack$c-top-minori stack$c-top-minori1)
             (stack$c-top-frame stack$c-top-frame1)
             (stack$c-top-minor-frame stack$c-top-minor-frame1)))



(define nth-nat ((n natp) (x true-listp))
  :returns (val natp :rule-classes :type-prescription)
  (nfix (nth n x))
  ///
  (defthm nth-nat-of-update-nth
    (equal (nth-nat m (update-nth n val l))
           (if (equal (nfix m) (nfix n))
               (nfix val)
             (nth-nat m l))))

  (fty::deffixequiv nth-nat))


(define stack$c-top-minori ((i natp :type (integer 0 *))
                            (stack$c))
  :guard (< i (stack$c-top-minor-length stack$c))
  :split-types t
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable nth-nat)))
  :prepwork ((local
              (defthm stack$c-top-minorp-implies-natp-nth
                (implies (and (stack$c-top-minorp x)
                              (< (nfix n) (len x)))
                         (natp (nth n x)))
                :hints(("Goal" :in-theory (enable nth len)))
                :rule-classes (:rewrite (:type-prescription :typed-term (nth n x))))))
  (mbe :logic (non-exec (nth-nat i (nth *stack$c-top-minori1* stack$c)))
       :exec (stack$c-top-minori1 i stack$c)))

(define stack$c-top-frame ((stack$c))
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable nth-nat)))
  (mbe :logic (nth-nat *stack$c-top-frame1* (non-exec stack$c))
       :exec (stack$c-top-frame1 stack$c)))

(define stack$c-top-minor-frame ((stack$c))
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable nth-nat)))
  (mbe :logic (nth-nat *stack$c-top-minor-frame1* (non-exec stack$c))
       :exec (stack$c-top-minor-frame1 stack$c)))

(defun-sk stack$c-minor-frames-welltyped (stack$c)
  (forall i
          (implies (natp i)
                   (and (gl-object-alist-p (nth (* 4 i) (nth *stack$c-minori* stack$c)))
                        (gl-objectlist-p (nth (+ 1 (* 4 i)) (nth *stack$c-minori* stack$c)))
                        (true-listp (nth (+ 2 (* 4 i)) (nth *stack$c-minori* stack$c))))))
  :rewrite :direct)

(in-theory (disable stack$c-minor-frames-welltyped
                    stack$c-minor-frames-welltyped-necc))

(local (in-theory (enable stack$c-minor-frames-welltyped-necc)))

(local
 (defthm stack$c-minor-frames-welltyped-zero
   (implies (stack$c-minor-frames-welltyped stack$c)
            (and (gl-object-alist-p (nth 0 (nth *stack$c-minori* stack$c)))
                 (gl-objectlist-p (nth 1 (nth *stack$c-minori* stack$c)))
                 (true-listp (nth 2 (nth *stack$c-minori* stack$c)))))
   :hints (("goal" :use ((:instance stack$c-minor-frames-welltyped-necc (i 0)))))))

;; (defthm stack$c-minor-frames-welltyped-implies-gl-object-alist-p
;;   (implies (and (stack$c-minor-frames-welltyped stack$c)
;;                 (posp n) (<= n (stack$c-nframes stack$c)))
;;            (gl-object-alist-p (nth (+ -3 (* 3 n)) (nth *stack$c-minori* stack$c))))
;;   :hints (("goal" :use ((:instance stack$c-minor-frames-welltyped-necc (i (1- n))))
;;            :in-theory (disable stack$c-minor-frames-welltyped-necc))))

;; (defthm stack$c-minor-frames-welltyped-implies-gl-objectlist-p
;;   (implies (and (stack$c-minor-frames-welltyped stack$c)
;;                 (posp n) (<= n (stack$c-nframes stack$c)))
;;            (gl-objectlist-p (nth (+ -2 (* 3 n)) (nth *stack$c-minori* stack$c))))
;;   :hints (("goal" :use ((:instance stack$c-minor-frames-welltyped-necc (i (1- n))))
;;            :in-theory (disable stack$c-minor-frames-welltyped-necc))))

(defun-sk stack$c-major-frames-welltyped (stack$c)
  (forall i
          (implies (natp i)
                   (gl-object-alist-p (nth (* 2 i) (nth *stack$c-majori* stack$c)))))
  :rewrite :direct)

(in-theory (disable stack$c-major-frames-welltyped
                    stack$c-major-frames-welltyped-necc))

(local (in-theory (enable stack$c-major-frames-welltyped-necc)))

(local
 (defthm stack$c-major-frames-welltyped-zero
   (implies (stack$c-major-frames-welltyped stack$c)
            (gl-object-alist-p (nth 0 (nth *stack$c-majori* stack$c))))
   :hints (("goal" :use ((:instance stack$c-major-frames-welltyped-necc (i 0)))))))


(defun-sk stack$c-top-minor-ordered (stack$c)
  (forall (i j)
          (implies (and (natp i)
                        (integerp j)
                        (< i j)
                        (<= j (stack$c-top-frame stack$c)))
                   (< (nth-nat i (nth *stack$c-top-minori1* stack$c))
                      (nth-nat j (nth *stack$c-top-minori1* stack$c)))))
  :rewrite :direct)

(in-theory (disable stack$c-top-minor-ordered
                    stack$c-top-minor-ordered-necc))

(local (in-theory (enable stack$c-top-minor-ordered-necc)))

(local
 (defthm stack$c-top-minor-ordered-lte
   (implies (and (stack$c-top-minor-ordered stack$c)
                 (natp i)
                 (integerp j)
                 (<= i j)
                 (<= j (stack$c-top-frame stack$c)))
            (and (<= (nth-nat i (nth *stack$c-top-minori1* stack$c))
                     (nth-nat j (nth *stack$c-top-minori1* stack$c)))
                 (< (nth-nat i (nth *stack$c-top-minori1* stack$c))
                    (+ 1 (nth-nat j (nth *stack$c-top-minori1* stack$c))))))
   :hints (("goal" :use ((:instance stack$c-top-minor-ordered-necc))
            :in-theory (disable stack$c-top-minor-ordered-necc)))))

(local
 (defthm stack$c-top-minor-ordered-minus1
   (implies (and (stack$c-top-minor-ordered stack$c)
                 (posp i)
                 (<= i (stack$c-top-frame stack$c)))
            (and (< (nth-nat (+ -1 i) (nth *stack$c-top-minori1* stack$c))
                    (nth-nat i (nth *stack$c-top-minori1* stack$c)))
                 (<= (+ 1 (nth-nat (+ -1 i) (nth *stack$c-top-minori1* stack$c)))
                     (nth-nat i (nth *stack$c-top-minori1* stack$c)))))
   :hints (("goal" :use ((:instance stack$c-top-minor-ordered-necc (i (+ -1 i)) (j i)))
            :in-theory (disable stack$c-top-minor-ordered-necc)))
   :rule-classes (:rewrite :linear)))

(local
 (defthm stack$c-top-minor-ordered-plus1
   (implies (and (stack$c-top-minor-ordered stack$c)
                 (natp i)
                 (< i (stack$c-top-frame stack$c)))
            (and (< (nth-nat i (nth *stack$c-top-minori1* stack$c))
                    (nth-nat (+ 1 i) (nth *stack$c-top-minori1* stack$c)))
                 (<= (+ 1 (nth-nat i (nth *stack$c-top-minori1* stack$c)))
                     (nth-nat (+ 1 i) (nth *stack$c-top-minori1* stack$c)))))
   :hints (("goal" :use ((:instance stack$c-top-minor-ordered-necc (i i) (j (+ 1 i))))
            :in-theory (disable stack$c-top-minor-ordered-necc)))
   :rule-classes (:rewrite :linear)))


(defun-sk stack$c-minor-frames-bounded (stack$c)
  (forall i
          (implies (and (natp i)
                        (<= (+ 4 (* 4 (nth-nat (stack$c-top-frame stack$c)
                                               (nth *stack$c-top-minori1* stack$c))))
                            i))
                   (equal (nth i (nth *stack$c-minori* stack$c)) nil)))
  :rewrite :direct)

(in-theory (disable stack$c-minor-frames-bounded
                    stack$c-minor-frames-bounded-necc))

(local (in-theory (enable stack$c-minor-frames-bounded-necc)))

(defun-sk stack$c-major-frames-bounded (stack$c)
  (forall i
          (implies (and (natp i)
                        (<= (+ 2 (* 2 (stack$c-top-frame stack$c)))
                            i))
                   (equal (nth i (nth *stack$c-majori* stack$c)) nil)))
  :rewrite :direct)

(in-theory (disable stack$c-major-frames-bounded
                    stack$c-major-frames-bounded-necc))

(local (in-theory (enable stack$c-major-frames-bounded-necc)))



(define stack$c-okp (stack$c)
  :enabled t
  (and (<= (+ 2 (* 2 (stack$c-top-frame stack$c))) (stack$c-major-length stack$c))
       (<= (+ 1 (stack$c-top-frame stack$c)) (stack$c-top-minor-length stack$c))
       (<= (+ 4 (* 4 (stack$c-top-minori (stack$c-top-frame stack$c) stack$c)))
           (stack$c-minor-length stack$c))
       (equal (stack$c-top-minor-frame stack$c)
              (stack$c-top-minori (stack$c-top-frame stack$c) stack$c))
       (ec-call (stack$c-top-minor-ordered stack$c))
       (ec-call (stack$c-major-frames-welltyped stack$c))
       (ec-call (stack$c-minor-frames-welltyped stack$c))
       (ec-call (stack$c-major-frames-bounded stack$c))
       (ec-call (stack$c-minor-frames-bounded stack$c))))

(local
 (encapsulate nil
   (local (defthm nth-of-cons-split
           (equal (nth n (cons a b))
                  (if (zp n)
                      a
                    (nth (+ -1 n) b)))
           :hints(("Goal" :in-theory (enable nth)))))
   (defthm stack$c-okp-of-create-stack$c
         (stack$c-okp (create-stack$c))
         :hints(("Goal" :in-theory (enable stack$c-major-frames-welltyped
                                           stack$c-minor-frames-welltyped
                                           stack$c-major-frames-bounded
                                           stack$c-minor-frames-bounded
                                           stack$c-top-minor-ordered
                                           nth))))))

(define stack$c-frames ((stack$c stack$c-okp))
  :enabled t
  (lposfix (+ 1 (stack$c-top-frame stack$c))))


(define maybe-grow-list ((threshold natp)
                         (default)
                         (list))
  :verify-guards nil
  :returns (new-list)
  (if (< (len list) (lnfix threshold))
      (resize-list list (max 16 (* 2 (lnfix threshold))) default)
    list)
  ///
  (defret len-of-maybe-grow-list-grows
    (<= (len list) (len new-list))
    :rule-classes :linear)

  (defret len-of-maybe-grow-list-sufficient
    (<= (nfix threshold) (len new-list))
    :rule-classes :linear)

  (defret nth-of-maybe-grow-list-under
    (implies (< (nfix n) (len list))
             (equal (nth n new-list) (nth n list))))

  (defthm nth-of-maybe-grow-list-when-default-nil
    (let ((new-list (maybe-grow-list threshold nil list)))
      (equal (nth n new-list) (nth n list))))

  (defthm nth-nat-of-maybe-grow-list
    (let ((new-list (maybe-grow-list threshold 0 list)))
      (equal (nth-nat n new-list) (nth-nat n list)))
    :hints(("Goal" :in-theory (enable nth-nat)))))

(local (defthmd update-nth-redundant-free
         (implies (and (equal val (nth n x))
                       (< (nfix n) (len x)))
                  (equal (update-nth n val x) x))
         :hints(("Goal" :in-theory (enable nth update-nth len)))))

(define stack$c-push-frame ((stack$c stack$c-okp))
  :enabled t
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable maybe-grow-list
                                          update-nth-redundant-free))))
  
  (b* ((prev-top-major (stack$c-top-frame stack$c))
       (new-major-len (+ 4 (* 2 prev-top-major)))
       (stack$c (mbe :logic (non-exec (update-nth *stack$c-majori*
                                                  (maybe-grow-list
                                                   new-major-len nil
                                                   (nth *stack$c-majori* stack$c))
                                                  stack$c))
                     :exec (if (< (stack$c-major-length stack$c) new-major-len)
                               (resize-stack$c-major (max 16 (* 2 new-major-len)) stack$c)
                             stack$c)))
       (new-top-len (+ 2 prev-top-major))
       (stack$c (mbe :logic (non-exec (update-nth *stack$c-top-minori1*
                                                  (maybe-grow-list
                                                   new-top-len 0
                                                   (nth *stack$c-top-minori1* stack$c))
                                                  stack$c))
                     :exec (if (< (stack$c-top-minor-length stack$c) new-top-len)
                               (resize-stack$c-top-minor (max 16 (* 2 new-top-len)) stack$c)
                             stack$c)))
       (prev-top-minor (stack$c-top-minor-frame stack$c))
       (new-minor-len (+ 8 (* 4 prev-top-minor)))
       (stack$c (mbe :logic (non-exec (update-nth *stack$c-minori*
                                                  (maybe-grow-list
                                                   new-minor-len nil
                                                   (nth *stack$c-minori* stack$c))
                                                  stack$c))
                     :exec (if (< (stack$c-minor-length stack$c) new-minor-len)
                               (resize-stack$c-minor (max 16 (* 2 new-minor-len)) stack$c)
                             stack$c)))
       (new-top-minor (+ 1 prev-top-minor))
       (stack$c (mbe :logic (b* ((stack$c (update-stack$c-top-minori (+ 1 prev-top-major) new-top-minor stack$c)))
                              (update-stack$c-top-minor-frame new-top-minor stack$c))
                     :exec (if (<= new-top-minor #xffffffff)
                               (b* ((stack$c (update-stack$c-top-minori (+ 1 prev-top-major) new-top-minor stack$c)))
                                 (update-stack$c-top-minor-frame new-top-minor stack$c))
                             (b* ((stack$c (ec-call (update-stack$c-top-minori (+ 1 prev-top-major) new-top-minor stack$c))))
                               (ec-call (update-stack$c-top-minor-frame new-top-minor stack$c))))))
       (new-top-major (+ 1 prev-top-major)))
    (mbe :logic (update-stack$c-top-frame new-top-major stack$c)
         :exec (if (<= new-top-major #xffffffff)
                   (update-stack$c-top-frame new-top-major stack$c)
                 (ec-call (update-stack$c-top-frame new-top-major stack$c))))))
       
(define stack$c-minor-frames ((stack$c stack$c-okp))
  :enabled t
  (b* ((top-major (stack$c-top-frame stack$c))
       (top-minor (stack$c-top-minori top-major stack$c))
       (prev-top-minor (if (eql 0 top-major)
                           -1
                         (stack$c-top-minori (+ -1 top-major) stack$c))))
    (- top-minor prev-top-minor)))

(define stack$c-push-minor-frame ((stack$c stack$c-okp))
  :enabled t
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable maybe-grow-list
                                          update-nth-redundant-free))))
  
  (b* ((top-major (stack$c-top-frame stack$c))
       (top-minor (stack$c-top-minor-frame stack$c))
       (new-top-minor (+ 1 top-minor))
       (new-minor-len (+ 4 (* 4 new-top-minor)))
       (stack$c (mbe :logic (non-exec (update-nth *stack$c-minori*
                                                  (maybe-grow-list
                                                   new-minor-len nil
                                                   (nth *stack$c-minori* stack$c))
                                                  stack$c))
                     :exec (if (< (stack$c-minor-length stack$c) new-minor-len)
                               (resize-stack$c-minor (max 16 (* 2 new-minor-len)) stack$c)
                             stack$c))))
    (mbe :logic
         (b* ((stack$c (update-stack$c-top-minori top-major new-top-minor stack$c)))
           (update-stack$c-top-minor-frame new-top-minor stack$c))
         :exec
         (if (<= new-top-minor #xffffffff)
             (b* ((stack$c (update-stack$c-top-minori top-major new-top-minor stack$c)))
               (update-stack$c-top-minor-frame new-top-minor stack$c))
           (b* ((stack$c (ec-call (update-stack$c-top-minori top-major new-top-minor stack$c))))
             (ec-call (update-stack$c-top-minor-frame new-top-minor stack$c)))))))
       
(define stack$c-set-bindings ((bindings gl-object-alist-p)
                              (stack$c stack$c-okp))
  :enabled t
  (b* ((top-major (stack$c-top-frame stack$c)))
    (update-stack$c-majori (* 2 top-major) bindings stack$c)))
       

(define stack$c-add-binding ((var pseudo-var-p)
                             (val gl-object-p)
                             (stack$c stack$c-okp))
  :enabled t
  (b* ((top-major (stack$c-top-frame stack$c))
       (index (* 2 top-major)))
    (update-stack$c-majori index (cons (cons var val) (stack$c-majori index stack$c))
                           stack$c)))

(define stack$c-set-debug (debug
                           (stack$c stack$c-okp))
  :enabled t
  (b* ((top-major (stack$c-top-frame stack$c)))
    (update-stack$c-majori (+ 1 (* 2 top-major)) debug stack$c)))

(define stack$c-set-minor-bindings ((bindings gl-object-alist-p)
                                    (stack$c stack$c-okp))
  :enabled t
  :guard-hints (("goal" :do-not-induct t))
  (b* ((top-minor (stack$c-top-minor-frame stack$c)))
    (update-stack$c-minori (* 4 top-minor) bindings stack$c)))

(define stack$c-add-minor-bindings ((bindings gl-object-alist-p)
                                    (stack$c stack$c-okp))
  :enabled t
  (b* ((top-minor (stack$c-top-minor-frame stack$c))
       (index (* 4 top-minor)))
    (update-stack$c-minori index
                           (append bindings (stack$c-minori index stack$c))
                           stack$c)))

(define stack$c-push-scratch ((obj gl-object-p)
                              (stack$c stack$c-okp))
  :enabled t
  (b* ((top-minor (stack$c-top-minor-frame stack$c))
       (index (+ 1 (* 4 top-minor))))
    (update-stack$c-minori index
                           (cons obj (stack$c-minori index stack$c))
                           stack$c)))

(define stack$c-push-bool-scratch ((bfr)
                                   (stack$c stack$c-okp))
  :enabled t
  (b* ((top-minor (stack$c-top-minor-frame stack$c))
       (index (+ 2 (* 4 top-minor))))
    (update-stack$c-minori index
                           (cons bfr (stack$c-minori index stack$c))
                           stack$c)))

(define stack$c-set-minor-debug ((debug)
                                 (stack$c stack$c-okp))
  :enabled t
  (b* ((top-minor (stack$c-top-minor-frame stack$c)))
    (update-stack$c-minori (+ 3 (* 4 top-minor)) debug stack$c)))

(define stack$c-bindings ((stack$c stack$c-okp))
  :enabled t
  (stack$c-majori (* 2 (stack$c-top-frame stack$c)) stack$c))

(define stack$c-minor-bindings ((stack$c stack$c-okp))
  :enabled t
  (b* ((top-minor (stack$c-top-minor-frame stack$c))
       (index (* 4 top-minor)))
    (stack$c-minori index stack$c)))

(define stack$c-debug ((stack$c stack$c-okp))
  :enabled t
  (stack$c-majori (+ 1 (* 2 (stack$c-top-frame stack$c))) stack$c))

(define stack$c-minor-debug ((stack$c stack$c-okp))
  :enabled t
  (b* ((top-minor (stack$c-top-minor-frame stack$c))
       (index (+ 3 (* 4 top-minor))))
    (stack$c-minori index stack$c)))

(define stack$c-scratch-len ((stack$c stack$c-okp))
  :enabled t
  (b* ((top-minor (stack$c-top-minor-frame stack$c))
       (index (+ 1 (* 4 top-minor))))
    (len (stack$c-minori index stack$c))))

(define stack$c-bool-scratch-len ((stack$c stack$c-okp))
  :enabled t
  (b* ((top-minor (stack$c-top-minor-frame stack$c))
       (index (+ 2 (* 4 top-minor))))
    (len (stack$c-minori index stack$c))))


(local (defthm true-listp-when-gl-objectlist-p-rw
         (implies (gl-objectlist-p x)
                  (true-listp x))))

(define stack$c-pop-scratch ((n natp)
                             (stack$c stack$c-okp))
  :enabled t
  :guard (<= n (stack$c-scratch-len stack$c))
  (b* ((top-minor (stack$c-top-minor-frame stack$c))
       (index (+ 1 (* 4 top-minor))))
    (update-stack$c-minori index (nthcdr n (stack$c-minori index stack$c)) stack$c)))

(define stack$c-pop-bool-scratch ((n natp)
                             (stack$c stack$c-okp))
  :enabled t
  :guard (<= n (stack$c-scratch-len stack$c))
  (b* ((top-minor (stack$c-top-minor-frame stack$c))
       (index (+ 2 (* 4 top-minor))))
    (update-stack$c-minori index (nthcdr n (stack$c-minori index stack$c)) stack$c)))

(define stack$c-scratch ((stack$c stack$c-okp))
  :enabled t
  (b* ((top-minor (stack$c-top-minor-frame stack$c))
       (index (+ 1 (* 4 top-minor))))
    (stack$c-minori index stack$c)))

(define stack$c-bool-scratch ((stack$c stack$c-okp))
  :enabled t
  (b* ((top-minor (stack$c-top-minor-frame stack$c))
       (index (+ 2 (* 4 top-minor))))
    (stack$c-minori index stack$c)))

(local (defthm bound-when-stack$c-top-minorp
         (implies (and (stack$c-top-minorp x)
                       (< (nfix n) (len x)))
                  (< (nth-nat n x) (expt 2 32)))
         :hints(("Goal" :in-theory (enable nth-nat nth len)))
         :rule-classes :linear))

(define stack$c-pop-minor-frame ((stack$c stack$c-okp))
  :enabled t
  :guard (< 1 (stack$c-minor-frames stack$c))
  (b* ((top-major (stack$c-top-frame stack$c))
       (top-minor (stack$c-top-minor-frame stack$c))
       (offset (* 4 top-minor))
       (stack$c (update-stack$c-minori offset nil stack$c))
       (stack$c (update-stack$c-minori (+ 1 offset) nil stack$c))
       (stack$c (update-stack$c-minori (+ 2 offset) nil stack$c))
       (stack$c (update-stack$c-minori (+ 3 offset) nil stack$c))
       (new-top-minor (+ -1 top-minor))
       (stack$c (update-stack$c-top-minori top-major new-top-minor stack$c)))
    (update-stack$c-top-minor-frame new-top-minor stack$c)))

(define stack$c-pop-frame ((stack$c stack$c-okp))
  :enabled t
  :guard (and (< 1 (stack$c-frames stack$c))
              (eql 1 (stack$c-minor-frames stack$c)))
  :prepwork ((local (defthm nth-nat-upper-bound-by-nth-dumb
                      (implies (and (< (nth n x) b)
                                    (posp b))
                               (< (+ -1 (nth-nat n x)) b))
                      :hints(("Goal" :in-theory (enable nth-nat nfix))))))
  (b* ((top-major (stack$c-top-frame stack$c))
       (top-minor (stack$c-top-minor-frame stack$c))
       (minor-offset (* 4 top-minor))
       (stack$c (update-stack$c-minori minor-offset nil stack$c))
       (stack$c (update-stack$c-minori (+ 1 minor-offset) nil stack$c))
       (stack$c (update-stack$c-minori (+ 2 minor-offset) nil stack$c))
       (stack$c (update-stack$c-minori (+ 3 minor-offset) nil stack$c))
       (major-offset (* 2 top-major))
       (stack$c (update-stack$c-majori major-offset nil stack$c))
       (stack$c (update-stack$c-majori (+ 1 major-offset) nil stack$c))
       (stack$c (update-stack$c-top-frame (+ -1 top-major) stack$c)))
    (update-stack$c-top-minor-frame (+ -1 top-minor) stack$c)))


(define stack$c-build-minor-frames ((bottom natp) (top natp) (stack$c stack$c-okp))
  :returns (frames minor-stack-p)
  :measure (lnfix top)
  :ruler-extenders (cons)
  :guard (<= (+ 4 (* 4 top)) (stack$c-minor-length stack$c))
  :enabled t
  (cons (make-minor-frame :bindings (stack$c-minori (* 4 (lnfix top)) stack$c)
                          :scratch (stack$c-minori (+ 1 (* 4 (lnfix top))) stack$c)
                          :bool-scratch (stack$c-minori (+ 2 (* 4 (lnfix top))) stack$c)
                          :debug (stack$c-minori (+ 3 (* 4 (lnfix top))) stack$c))
        (and (< (lnfix bottom) (lnfix top))
             (stack$c-build-minor-frames bottom (1- (lnfix top)) stack$c)))
  ///
  (defthm len-of-stack$c-build-minor-frames
    (equal (len (stack$c-build-minor-frames bottom top stack$c))
           (pos-fix (+ 1 (- (nfix top) (nfix bottom)))))
    :hints(("Goal" :in-theory (enable len pos-fix)))))

(define stack$c-build-major-frames ((top natp) (stack$c stack$c-okp))
  :returns (frames major-stack-p)
  :measure (lnfix top)
  :ruler-extenders (cons)
  :guard (<= top (stack$c-top-frame stack$c))
  :guard-hints (("goal" :use ((:instance stack$c-top-minor-ordered-necc
                               (i top) (j (stack$c-top-frame stack$c))))
                 :in-theory (disable stack$c-top-minor-ordered-necc)))
  :enabled t
  (cons (make-major-frame :bindings (stack$c-majori (* 2 (lnfix top)) stack$c)
                          :debug (stack$c-majori (+ 1 (* 2 (lnfix top))) stack$c)
                          :minor-stack (stack$c-build-minor-frames
                                        (if (zp top)
                                            0
                                          (+ 1 (stack$c-top-minori (1- (lnfix top)) stack$c)))
                                        (stack$c-top-minori (lnfix top) stack$c)
                                        stack$c))
        (and (posp top)
             (stack$c-build-major-frames (1- (lnfix top)) stack$c)))
  ///
  
  (defthm len-of-stack$c-build-major-frames
    (equal (len (stack$c-build-major-frames top stack$c))
           (+ 1 (nfix top)))
    :hints(("Goal" :in-theory (enable len)))))

(local (defsection range-nat-equiv
         (defthmd nth-nat-when-range-nat-equiv
           (implies (and (stobjs::range-nat-equiv start num x y)
                         (<= (nfix start) (nfix n))
                         (< (nfix n) (+ (nfix start) (nfix num))))
                    (equal (nth-nat n x) (nth-nat n y)))
           :hints(("Goal" :in-theory (enable nth-nat stobjs::nth-when-range-nat-equiv))))

         (defthm range-nat-equiv-by-badguy-nth-nat
           (let ((badguy (stobjs::range-nat-equiv-badguy start num x y)))
             (implies (equal (nth-nat badguy x) (nth-nat badguy y))
                      (stobjs::range-nat-equiv start num x y)))
           :hints (("Goal" :in-theory (enable nth-nat))))
           

         (defthm range-nat-equiv-by-badguy-literal-nth-nat
           (let ((badguy (stobjs::range-nat-equiv-badguy start num x y)))
             (implies (acl2::rewriting-positive-literal `(stobjs::range-nat-equiv ,start ,num ,x ,y))
                      (iff (stobjs::range-nat-equiv start num x y)
                           (or (not (< badguy (+ (nfix start) (nfix num))))
                               (equal (nth-nat badguy x) (nth-nat badguy y))))))
           :hints(("Goal" :in-theory (enable stobjs::range-nat-equiv-by-badguy-literal
                                             stobjs::nth-when-range-nat-equiv
                                             nth-nat))))

         (defthm range-nat-equiv-by-superrange1
           (implies (and (stobjs::range-nat-equiv min1 max1 x y)
                         (<= (nfix min1) (nfix min))
                         (<= (+ (nfix min) (nfix max))
                             (+ (nfix min1) (nfix max1))))
                    (stobjs::range-nat-equiv min max x y))
           :hints(("Goal" :in-theory (disable range-nat-equiv-by-badguy-literal-nth-nat))))

         (defthm range-nat-equiv-when-range-nat-equiv1
           (implies (stobjs::range-nat-equiv start num x y)
                    (stobjs::range-nat-equiv start num x y)))))

(local
 (defthm stack$c-build-minor-frames-of-update
   (implies (and (bind-free (stobjs::bind-updater-independence-prev-stobj new mfc state))
                 (syntaxp (not (equal new old)))
                 (<= (nfix bottom) (nfix top))
                 (stobjs::range-equal (* 4 (nfix bottom))
                                      (+ 4 (* 4 (- (nfix top) (nfix bottom))))
                                      (nth *stack$c-minori* new)
                                      (nth *stack$c-minori* old)))
            (equal (stack$c-build-minor-frames bottom top new)
                   (stack$c-build-minor-frames bottom top old)))
   :hints (("goal" :induct (stack$c-build-minor-frames bottom top new)
            :expand ((:free (new) (stack$c-build-minor-frames bottom top new)))
            :in-theory (enable stobjs::nth-when-range-equal)))))


(local
 (defsection stack$c-build-major-frames-of-update
   (local (defthm zp-forwrad-to-nat-equiv-0
            (implies (zp x)
                     (acl2::nat-equiv x 0))
            :rule-classes :forward-chaining))

   (local
    (defthmd stack$c-build-major-frames-of-update-lemma
      (let ((top-minor (nth-nat top (nth *stack$c-top-minori1* old))))
        (implies (and (bind-free (stobjs::bind-updater-independence-prev-stobj new mfc state))
                      (stack$c-top-minor-ordered old)
                      (<= (nfix top) (stack$c-top-frame old))
                      (stobjs::range-equal 0 (+ 2 (* 2 (nfix top)))
                                           (nth *stack$c-majori* new)
                                           (nth *stack$c-majori* old))
                      (stobjs::range-nat-equiv 0 (+ 1 (nfix top))
                                               (nth *stack$c-top-minori1* new)
                                               (nth *stack$c-top-minori1* old))
                      ;; (equal top-minor (nth-nat top (nth *stack$c-top-minori1* old)))
                      (stobjs::range-equal 0 (+ 4 (* 4 top-minor))
                                           (nth *stack$c-minori* new)
                                           (nth *stack$c-minori* old)))
                 (equal (stack$c-build-major-frames top new)
                        (stack$c-build-major-frames top old))))
      :hints (("goal" :induct (stack$c-build-major-frames top new)
               :expand ((:free (new) (stack$c-build-major-frames top new)))
               :in-theory (enable stobjs::nth-when-range-equal
                                  nth-nat-when-range-nat-equiv)
               :do-not-induct t))))

   (defthm stack$c-build-major-frames-of-update
     (implies (and (bind-free (stobjs::bind-updater-independence-prev-stobj new mfc state))
                   (syntaxp (not (equal new old)))
                   (stack$c-top-minor-ordered old)
                   (<= (nfix top) (stack$c-top-frame old))
                   (stobjs::range-equal 0 (+ 2 (* 2 (nfix top)))
                                        (nth *stack$c-majori* new)
                                        (nth *stack$c-majori* old))
                   (stobjs::range-nat-equiv 0 (+ 1 (nfix top))
                                            (nth *stack$c-top-minori1* new)
                                            (nth *stack$c-top-minori1* old))
                   (equal top-minor (nth-nat top (nth *stack$c-top-minori1* old)))
                   (stobjs::range-equal 0 (+ 4 (* 4 top-minor))
                                        (nth *stack$c-minori* new)
                                        (nth *stack$c-minori* old)))
              (equal (stack$c-build-major-frames top new)
                     (stack$c-build-major-frames top old)))
     :hints (("goal" :use stack$c-build-major-frames-of-update-lemma)))))


(define stack$c-extract ((stack$c stack$c-okp))
  :enabled t
  (stack$c-build-major-frames (stack$c-top-frame stack$c) stack$c))
     






(local
 (progn
   (define stack-corr (stack$c stack$a)
     :non-executable t
     :enabled t
     :verify-guards nil
     (and (stack$c-okp stack$c)
          (equal (stack$c-build-major-frames (stack$c-top-frame stack$c) stack$c) stack$a)))


   (defthm nth-of-cons-split
     (equal (nth n (cons a b))
            (if (zp n)
                a
              (nth (+ -1 n) b)))
     :hints(("Goal" :in-theory (enable nth))))

   (defthm max-when-gte
     (implies (and (<= a b)
                   (integerp a) (integerp b))
              (equal (max a b) b))
     :hints(("Goal" :in-theory (enable max))))


   (defthm equal-plus-consts
     (implies (syntaxp (and (quotep a) (quotep b)))
              (equal (equal (+ a c) (+ b d))
                     (equal (+ (+ (- b) a) c) (fix d)))))

   (defthm equal-const-plus-4*
     (implies (syntaxp (quotep c))
              (equal (equal (+ c (* 4 x)) (* 4 y))
                     (equal (+ (/ c 4) x) (fix y)))))


   (defthm equal-const-plus-2*
     (implies (syntaxp (quotep c))
              (equal (equal (+ c (* 2 x)) (* 2 y))
                     (equal (+ (/ c 2) x) (fix y)))))


   (in-theory (disable (stack$c-build-major-frames)
                       (stack$c-build-minor-frames)))


   (defthm stack$c-build-minor-frames-of-update-hack
     (implies (and (bind-free '((old . stack$c)))
                   (syntaxp (not (equal new old)))
                   (<= (nfix bottom) (nfix top))
                   (stobjs::range-equal (* 4 (nfix bottom))
                                        (+ 4 (* 4 (- (nfix top) (nfix bottom))))
                                        (nth *stack$c-minori* new)
                                        (nth *stack$c-minori* old)))
              (equal (stack$c-build-minor-frames bottom top new)
                     (stack$c-build-minor-frames bottom top old)))
     :hints (("goal" :use stack$c-build-minor-frames-of-update
              :in-theory (disable stack$c-build-minor-frames-of-update))))

   (defthm stack$c-build-major-frames-of-update-hack
     (implies (and (bind-free '((old . stack$c)))
                   (syntaxp (not (equal new old)))
                   (stack$c-top-minor-ordered old)
                   (<= (nfix top) (stack$c-top-frame old))
                   (stobjs::range-equal 0 (+ 2 (* 2 (nfix top)))
                                        (nth *stack$c-majori* new)
                                        (nth *stack$c-majori* old))
                   (stobjs::range-nat-equiv 0 (+ 1 (nfix top))
                                            (nth *stack$c-top-minori1* new)
                                            (nth *stack$c-top-minori1* old))
                   (equal top-minor (nth-nat top (nth *stack$c-top-minori1* old)))
                   (stobjs::range-equal 0 (+ 4 (* 4 top-minor))
                                        (nth *stack$c-minori* new)
                                        (nth *stack$c-minori* old)))
              (equal (stack$c-build-major-frames top new)
                     (stack$c-build-major-frames top old)))
     :hints (("goal" :use stack$c-build-major-frames-of-update
              :in-theory (disable stack$c-build-major-frames-of-update))))

   (defthm nth-0-stack$c-build-major-frames
     (equal (nth 0 (stack$c-build-major-frames top stack$c))
            (car (stack$c-build-major-frames top stack$c))))

   (defthm car-stack$c-build-major-frames
     (equal (car (stack$c-build-major-frames top stack$c))
            (MAKE-MAJOR-FRAME
             :BINDINGS (STACK$C-MAJORI (* 2 (LNFIX TOP))
                                       STACK$C)
             :DEBUG (STACK$C-MAJORI (+ 1 (* 2 (LNFIX TOP)))
                                    STACK$C)
             :MINOR-STACK
             (STACK$C-BUILD-MINOR-FRAMES
              (IF (ZP TOP)
                  0
                  (+ 1
                     (STACK$C-TOP-MINORI (1- (LNFIX TOP))
                                         STACK$C)))
              (STACK$C-TOP-MINORI (LNFIX TOP) STACK$C)
              STACK$C))))

   (defthm stack$c-build-major-frames-0
     (equal (stack$c-build-major-frames 0 stack$c)
            (list (MAKE-MAJOR-FRAME
                   :BINDINGS (STACK$C-MAJORI 0
                                             STACK$C)
                   :DEBUG (STACK$C-MAJORI 1
                                          STACK$C)
                   :MINOR-STACK
                   (STACK$C-BUILD-MINOR-FRAMES 0
                                               (STACK$C-TOP-MINORI 0 STACK$C)
                                               STACK$C)))))

   (defthm stack$c-build-major-frames-plus1
     (implies (natp top)
              (equal (stack$c-build-major-frames (+ 1 top) stack$c)
                     (cons (let ((top (+ 1 top)))
                             (MAKE-MAJOR-FRAME
                              :BINDINGS (STACK$C-MAJORI (* 2 (LNFIX TOP))
                                                        STACK$C)
                              :DEBUG (STACK$C-MAJORI (+ 1 (* 2 (LNFIX TOP)))
                                                     STACK$C)
                              :MINOR-STACK
                              (STACK$C-BUILD-MINOR-FRAMES
                               (IF (ZP TOP)
                                   0
                                   (+ 1
                                      (STACK$C-TOP-MINORI (1- (LNFIX TOP))
                                                          STACK$C)))
                               (STACK$C-TOP-MINORI (LNFIX TOP) STACK$C)
                               STACK$C)))
                           (stack$c-build-major-frames top stack$c)))))

   (defthm nth-0-stack$C-build-minor-frames
     (equal (nth 0 (stack$c-build-minor-frames bottom top stack$c))
            (car (stack$c-build-minor-frames bottom top stack$c))))

   (defthm car-stack$C-build-minor-frames
     (equal (car (stack$c-build-minor-frames bottom top stack$c))
            (MAKE-MINOR-FRAME
             :BINDINGS (STACK$C-MINORI (* 4 (LNFIX TOP))
                                       STACK$C)
             :SCRATCH (STACK$C-MINORI (+ 1 (* 4 (LNFIX TOP)))
                                      STACK$C)
             :bool-SCRATCH (STACK$C-MINORI (+ 2 (* 4 (LNFIX TOP)))
                                           STACK$C)
             :DEBUG (STACK$C-MINORI (+ 3 (* 4 (LNFIX TOP)))
                                    STACK$C))))

   (defthm stack$C-build-minor-frames-zero
     (equal (stack$c-build-minor-frames top top stack$c)
            (list (MAKE-MINOR-FRAME
                   :BINDINGS (STACK$C-MINORI (* 4 (LNFIX TOP))
                                             STACK$C)
                   :SCRATCH (STACK$C-MINORI (+ 1 (* 4 (LNFIX TOP)))
                                            STACK$C)
                   :bool-SCRATCH (STACK$C-MINORI (+ 2 (* 4 (LNFIX TOP)))
                                                 STACK$C)
                   :DEBUG (STACK$C-MINORI (+ 3 (* 4 (LNFIX TOP)))
                                          STACK$C)))))

   (defthm stack$C-build-minor-frames-plus-1
     (implies (and (<= (nfix bottom) top)
                   (natp top))
              (equal (stack$c-build-minor-frames bottom (+ 1 top) stack$c)
                     (cons (let ((top (+ 1 top)))
                             (MAKE-MINOR-FRAME
                              :BINDINGS (STACK$C-MINORI (* 4 (LNFIX TOP))
                                                        STACK$C)
                              :SCRATCH (STACK$C-MINORI (+ 1 (* 4 (LNFIX TOP)))
                                                       STACK$C)
                              :bool-SCRATCH (STACK$C-MINORI (+ 2 (* 4 (LNFIX TOP)))
                                                            STACK$C)
                              :DEBUG (STACK$C-MINORI (+ 3 (* 4 (LNFIX TOP)))
                                                     STACK$C)))
                           (stack$c-build-minor-frames bottom top stack$c)))))

   (defthm stack$c-top-minor-ordered-lemma
     (implies (and (stack$c-top-minor-ordered stack$c)
                   (natp i)
                   (integerp j)
                   (< i j)
                   (<= j (stack$c-top-frame stack$c))
                   (< 1 (- (nth-nat j (nth *stack$c-top-minori1* stack$C))
                           (nth-nat (+ -1 j) (nth *stack$c-top-minori1* stack$C)))))
              (< (nth-nat i (nth *stack$c-top-minori1* stack$C))
                 (+ -1 (nth-nat j (nth *stack$c-top-minori1* stack$c)))))
     :hints (("goal" :use ((:instance stack$c-top-minor-ordered-necc
                            (i i) (j (+ -1 j))))
              :in-theory (disable stack$c-top-minor-ordered-necc))))

   

   (include-book "clause-processors/generalize" :dir :system)
   (include-book "clause-processors/find-subterms" :dir :system)

   (set-default-hints
    '((and stable-under-simplificationp
           (let* ((lit (car (last clause)))
                  (hint
                   (cond ((member (car lit)
                                  '(stack$c-major-frames-welltyped
                                    stack$c-minor-frames-welltyped
                                    stack$c-major-frames-bounded
                                    stack$c-minor-frames-bounded
                                    stack$c-top-minor-ordered
                                    ))
                          (let ((witness-sym (intern-in-package-of-symbol
                                              (concatenate 'string (symbol-name (car lit)) "-WITNESS")
                                              (car lit)))
                                (witness-sym2 (intern-in-package-of-symbol
                                               (concatenate 'string (symbol-name (car lit)) "-WITNESS2")
                                               (car lit))))
                            `(:computed-hint-replacement
                              ((let* ((call (acl2::find-call-lst ',witness-sym clause)))
                                 (and call
                                      `(:clause-processor
                                        (acl2::generalize-with-alist-cp
                                         clause '((,call . ,',witness-sym)
                                                  ((mv-nth '2 ,call) . ,',witness-sym2)
                                                  ))))))
                              :expand (,lit))))
                         (t ;; (acl2::find-call 'stack$c-build-major-frames lit)
                          `(;; :computed-hint-replacement t
                            :expand ((:free (stack$c1)
                                      (stack$c-build-major-frames (nth-nat *stack$c-top-frame1* stack$c)
                                                                  stack$c1))
                                     (:free (bottom stack$c1)
                                      (stack$c-build-minor-frames bottom
                                                                  (nth-nat (nth-nat *stack$c-top-frame1* stack$c)
                                                                           (nth *stack$c-top-minori1* stack$c))
                                                                  stack$c1))
                                     (:free (stack$c1)
                                      (stack$c-build-minor-frames 0
                                                                  (nth-nat 0
                                                                           (nth *stack$c-top-minori1* stack$c))
                                                                  stack$c1))))))))
             ;; (prog2$ (cw "hint: ~x0~%" hint)
             hint))))

   (in-theory (disable stack$c-build-minor-frames
                       stack$c-build-major-frames
                       cons-equal
                       true-listp-update-nth
                       acl2::nth-when-too-large-cheap
                       ;; len-stack-when-atom-cdr
                       stack$c-top-minorp
                       unsigned-byte-p
                       acl2::nfix-when-not-natp
                       acl2::nth-when-atom))
   
   ))

(defabsstobj-events stack
  :concrete stack$c
  :corr-fn stack-corr
  :recognizer (stackp :logic major-stack-p
                      :exec stack$cp)
  :creator (create-stack :logic create-stack$a
                         :exec create-stack$c)
  :exports ((stack-frames :logic stack$a-frames :exec stack$c-frames)
            (stack-push-frame :logic stack$a-push-frame :exec stack$c-push-frame :protect t)
            (stack-minor-frames :logic stack$a-minor-frames :exec stack$c-minor-frames)
            (stack-push-minor-frame :logic stack$a-push-minor-frame :exec stack$c-push-minor-frame :protect t)
            (stack-set-bindings :logic stack$a-set-bindings :exec stack$c-set-bindings)
            (stack-add-binding :logic stack$a-add-binding :exec stack$c-add-binding)
            (stack-set-debug :logic stack$a-set-debug :exec stack$c-set-debug)
            (stack-set-minor-bindings :logic stack$a-set-minor-bindings :exec stack$c-set-minor-bindings)
            (stack-add-minor-bindings :logic stack$a-add-minor-bindings :exec stack$c-add-minor-bindings)
            (stack-push-scratch :logic stack$a-push-scratch :exec stack$c-push-scratch)
            (stack-push-bool-scratch :logic stack$a-push-bool-scratch :exec stack$c-push-bool-scratch)
            (stack-set-minor-debug :logic stack$a-set-minor-debug :exec stack$c-set-minor-debug)
            (stack-bindings :logic stack$a-bindings :exec stack$c-bindings)
            (stack-minor-bindings :logic stack$a-minor-bindings :exec stack$c-minor-bindings)
            (stack-debug :logic stack$a-debug :exec stack$c-debug)
            (stack-minor-debug :logic stack$a-minor-debug :exec stack$c-minor-debug)
            (stack-scratch-len :logic stack$a-scratch-len :exec stack$c-scratch-len)
            (stack-pop-scratch :logic stack$a-pop-scratch :exec stack$c-pop-scratch)
            (stack-scratch :logic stack$a-scratch :exec stack$c-scratch)
            (stack-bool-scratch-len :logic stack$a-bool-scratch-len :exec stack$c-bool-scratch-len)
            (stack-pop-bool-scratch :logic stack$a-pop-bool-scratch :exec stack$c-pop-bool-scratch)
            (stack-bool-scratch :logic stack$a-bool-scratch :exec stack$c-bool-scratch)
            (stack-pop-minor-frame :logic stack$a-pop-minor-frame :exec stack$c-pop-minor-frame :protect t)
            (stack-pop-frame :logic stack$a-pop-frame :exec stack$c-pop-frame :protect t)
            (stack-extract :logic stack$a-extract :exec stack$c-extract)))




(define revappend-take ((n natp) (x true-listp) acc)
  (if (zp n)
      acc
    (revappend-take (1- n) (cdr x) (cons (car x) acc)))
  ///
  (defthm revappend-take-elim
    (equal (revappend-take n x acc)
           (revappend (take n x) acc))))

(define rev-take ((n natp) (x true-listp))
  :inline t
  (revappend-take n x nil)
  ///
  (defthm rev-take-elim
    (equal (rev-take n x)
           (rev (take n x)))))

(define stack-peek-scratch ((n natp) stack)
  :guard (<= n (stack-scratch-len stack))
  (rev-take n (stack-scratch stack)))

