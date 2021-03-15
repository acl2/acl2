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

(include-book "std/stobjs/absstobjs" :dir :System)
(include-book "scratch-nontagidx")
(include-book "stack-logic")
(include-book "std/stobjs/updater-independence" :dir :system)
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))

(local (include-book "std/util/termhints" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))


(local (include-book "scratchobj"))

(local (in-theory (enable* acl2::arith-equiv-forwarding)))

(local (fty::deflist fgl-objectlist :elt-type fgl-object :true-listp t :elementp-of-nil t))

(local (in-theory (disable nth acl2::nth-when-zp update-nth (tau-system))))

(local (in-theory (disable unsigned-byte-p signed-byte-p
                           bitops::logand-with-negated-bitmask)))

(local (std::add-default-post-define-hook :fix))



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


;; The stobj implementation of the stack has 5 arrays:
;; - one each for the major & minor frames' interleaved bindings and debug fields (3 total)
;;         (that is, bindings, term, term-index for minor frames; bindings, rule, phase for major frames)
;; - one for the top minor frame pointer of each major frame except the topmost
;; - one for the next scratch element of each minor frame except the topmost
;;    (or equivalently, the bottom scratch element of each minor frame except the bottommost).
;; - one for all the scratch objects.

;; other elements: 
;;  - top major frame pointer
;;  - top minor frame pointer
;;  - next scratch element pointer.

;; (Note: there is always at least 1 major frame and at least 1 minor frame per
;; major frame, whereas there may be 0 stack elements, which is why the
;; asymmetry.)

;; A major frame's bottommost minor stack frame is frame 0 for major frame 0,
;; and the frame after the previous major frame's topmost minor stack frame for
;; others.

;; The scratch array is an array of untyped objects.  Every 16th object
;; (beginning at 0) is an integer that encodes the scratchobj kinds for the
;; following 15 objects in 4-bit chunks (total 60 bits).  Since we only have 6
;; kinds of scratchobj, that gives us room to grow up to 16.

(encapsulate
  ()

  (local (in-theory (enable len)))
  (fty::deflist scratch-nontagidxlist :elt-type scratch-nontagidx :true-listp t))

(defstobj stack$c
  (stack$c-minor :type (array t (3)) :resizable t)
  (stack$c-major :type (array t (3)) :resizable t)
  (stack$c-scratch :type (array t (2)) :resizable t :initially 0)
  (stack$c-frame-top-minor :type (array (unsigned-byte 32) (0)) :resizable t :initially 0)
  (stack$c-frame-next-scratch :type (array (and (unsigned-byte 32)
                                                (satisfies scratch-nontagidx-p))
                                           (0))
                              :resizable t :initially 1)
  (stack$c-top-frame :type (unsigned-byte 32) :initially 0)
  (stack$c-top-minor :type (unsigned-byte 32) :initially 0)
  (stack$c-next-scratch :type (and (unsigned-byte 32)
                                   (satisfies scratch-nontagidx-p))
                        :initially 1)
  :renaming ((stack$c-frame-top-minori stack$c-frame-top-minori1)
             (stack$c-frame-next-scratchi stack$c-frame-next-scratchi1)
             (stack$c-top-frame stack$c-top-frame1)
             (stack$c-top-minor stack$c-top-minor1)
             (stack$c-next-scratch stack$c-next-scratch1)
             (update-stack$c-frame-top-minori update-stack$c-frame-top-minori1)
             (update-stack$c-frame-next-scratchi update-stack$c-frame-next-scratchi1)
             (update-stack$c-top-frame update-stack$c-top-frame1)
             (update-stack$c-top-minor update-stack$c-top-minor1)
             (update-stack$c-next-scratch update-stack$c-next-scratch1)
             (stack$c-scratchi stack$c-scratchi1)
             (update-stack$c-scratchi update-stack$c-scratchi1)))

(local (include-book "centaur/misc/u32-listp" :dir :system))

(local (defthm stack$c-frame-next-scratchp-equals
         (equal (stack$c-frame-next-scratchp x)
                (and (acl2::u32-listp x)
                     (scratch-nontagidxlist-p x)))))




(defthm nth-of-update-nth-array
  (equal (nth n (update-nth-array i j v x))
         (if (equal (nfix n) (nfix i))
             (update-nth j v (nth n x))
           (nth n x))))



(local (in-theory (disable update-nth-array)))


(define nth-nat ((n natp) (x true-listp))
  :returns (val natp :rule-classes :type-prescription)
  (nfix (nth n x))
  ///
  (defthm nth-nat-of-update-nth
    (equal (nth-nat m (update-nth n val l))
           (if (equal (nfix m) (nfix n))
               (nfix val)
             (nth-nat m l))))

  (fty::deffixequiv nth-nat)

  (def-updater-independence-thm nth-nat-when-nth-nat-equiv
    (implies (acl2::nat-equiv (nth n new) (nth n old))
             (equal (nth-nat n new) (nth-nat n old))))

  (defthm unsigned-byte-p-of-nth-nat
    (implies (unsigned-byte-p k (nth n x))
             (unsigned-byte-p k (nth-nat n x))))

  (defthm nth-nat-of-update-nth-array
    (implies (not (equal (nfix n) (nfix i)))
             (equal (nth-nat n (update-nth-array i j v x))
                    (nth-nat n x)))
    :hints(("Goal" :in-theory (enable update-nth-array)))))


(define nth-nontag ((n natp) (x scratch-nontagidxlist-p))
  :guard (< n (len x))
  :returns (val scratch-nontagidx-p
                :rule-classes (:rewrite
                               (:type-prescription :typed-term val)))
  (scratch-nontagidx-fix (nth n x))
  ///
  (defthm nth-nontag-of-update-nth
    (equal (nth-nontag m (update-nth n val l))
           (if (equal (nfix m) (nfix n))
               (scratch-nontagidx-fix val)
             (nth-nontag m l)))
    :hints (("Goal" :in-theory
             (disable (:rewrite nth-of-scratch-nontagidxlist-fix)))))


  (fty::deffixcong scratch-nontagidxlist-equiv scratch-nontagidx-equiv (nth n x) x
                   :hints(("Goal" :in-theory (e/d (scratch-nontagidxlist-fix nth)
                                                  ((:rewrite nth-of-scratch-nontagidxlist-fix)))
                           :induct (nth n x))))

  (fty::deffixequiv nth-nontag)

  (def-updater-independence-thm nth-nontag-when-nth-nontag-equiv
    (implies (scratch-nontagidx-equiv (nth n new) (nth n old))
             (equal (nth-nontag n new) (nth-nontag n old))))

  (defthm unsigned-byte-p-of-nth-nontag
    (implies (and (unsigned-byte-p k (nth n x))
                  (not (equal 0 k)))
             (unsigned-byte-p k (nth-nontag n x))))

  (defthm nth-nontag-of-update-nth-array
    (implies (not (equal (nfix n) (nfix i)))
             (equal (nth-nontag n (update-nth-array i j v x))
                    (nth-nontag n x)))
    :hints(("Goal" :in-theory (enable update-nth-array)))))


(define update-nth-scratch ((n natp) val (x true-listp))
  :hooks nil
  (if (zp n)
      (cons val (cdr x))
    (cons (if (atom x) 0 (car x))
          (update-nth-scratch (1- n) val (cdr x))))
  ///
  (local (defthm len-of-update-nth-scratch-nil
           (equal (len (update-nth-scratch n val nil))
                  (+ 1 (nfix n)))
           :hints(("Goal" :in-theory (enable len)))))

  (defthmd len-of-update-nth-scratch
    (equal (len (update-nth-scratch n val x))
           (max (+ 1 (nfix n)) (len x)))
    :hints(("Goal" :in-theory (enable max len))))

  (defthmd update-nth-scratch-when-less
    (implies (<= (nfix n) (len x))
             (equal (update-nth-scratch n val x)
                    (update-nth n val x)))
    :hints(("Goal" :in-theory (enable update-nth len))))
  
  (acl2::set-prev-stobjs-correspondence update-nth-scratch :stobjs-out (stobj) :formals (n val stobj))

  (fty::deffixequiv update-nth-scratch :args (n)))

(define update-nth-scratch-array ((n natp) (i natp) val (x true-listp))
  :verify-guards nil
  :hooks nil
  (update-nth n
              (update-nth-scratch i val (nth n x))
              x)
  ///
  (defthm nth-of-update-nth-scratch-array
    (equal (nth m (update-nth-scratch-array n i val x))
           (if (equal (nfix m) (nfix n))
               (update-nth-scratch i val (nth n x))
             (nth m x))))

  (defthm nth-nat-of-update-nth-scratch-array
    (implies (not (equal (nfix m) (nfix n)))
             (equal (nth-nat m (update-nth-scratch-array n i val x))
                    (nth-nat m x))))

  (defthm nth-nontag-of-update-nth-scratch-array
    (implies (not (equal (nfix n) (nfix i)))
             (equal (nth-nontag n (update-nth-scratch-array i j v x))
                    (nth-nontag n x)))
    :hints(("Goal" :in-theory (enable update-nth-scratch-array))))
  
  (acl2::set-prev-stobjs-correspondence update-nth-scratch-array :stobjs-out (stobj) :formals (j k val stobj))

  (fty::deffixequiv update-nth-scratch-array :args (n i)))

(define nth-scratch ((n natp) (x true-listp))
  (if (< (nfix n) (len x))
      (nth n x)
    0)
  ///
  (local (defun nth-scratch-of-update-ind (m n l)
           (if (or (zp m) (zp n))
               l
             (nth-scratch-of-update-ind (1- m) (1- n) (cdr l)))))

  (defthm nth-scratch-of-update-nth-scratch
    (equal (nth-scratch m (update-nth-scratch n val l))
           (if (equal (nfix m) (nfix n))
               val
             (nth-scratch m l)))
    :hints(("Goal" :in-theory (enable nth update-nth-scratch len)
            :induct (nth-scratch-of-update-ind m n l)
            :expand ((update-nth-scratch n val l)
                     (update-nth-scratch (len l) val l)
                     (:free (x) (nth m x)))))))

(define stack$c-scratchi ((i natp :type (integer 0 *))
                          (stack$c))
  :guard (< i (stack$c-scratch-length stack$c))
  :prepwork ((local (in-theory (enable nth-scratch))))
  :inline t
  :enabled t
  (mbe :logic (non-exec (nth-scratch i (nth *stack$c-scratchi1* stack$c)))
       :exec (stack$c-scratchi1 i stack$c)))

(define update-stack$c-scratchi ((i natp :type (integer 0 *))
                                 val
                                 (stack$c))
  :guard (< i (stack$c-scratch-length stack$c))
  :prepwork ((local (in-theory (enable nth-scratch
                                       update-nth-scratch-array
                                       update-nth-array
                                       update-nth-scratch-when-less))))
  :inline t
  :enabled t
  (mbe :logic (non-exec (update-nth-scratch-array *stack$c-scratchi1* i val stack$c))
       :exec (update-stack$c-scratchi1 i val stack$c)))





(define stack$c-frame-top-minori ((i natp :type (integer 0 *))
                                  (stack$c))
  :guard (< i (stack$c-frame-top-minor-length stack$c))
  :split-types t
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable nth-nat)))
  :prepwork ((local
              (defthm stack$c-frame-top-minorp-implies-natp-nth
                (implies (and (stack$c-frame-top-minorp x)
                              (< (nfix n) (len x)))
                         (natp (nth n x)))
                :hints(("Goal" :in-theory (enable nth len)))
                :rule-classes (:rewrite (:type-prescription :typed-term (nth n x))))))
  (mbe :logic (non-exec (nth-nat i (nth *stack$c-frame-top-minori1* stack$c)))
       :exec (stack$c-frame-top-minori1 i stack$c)))



(define stack$c-top-minor ((stack$c))
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable nth-nat)))
  (mbe :logic (nth-nat *stack$c-top-minor1* (non-exec stack$c))
       :exec (stack$c-top-minor1 stack$c)))

(define stack$c-frame-next-scratchi ((i natp :type (integer 0 *))
                                     (stack$c))
  :guard (< i (stack$c-frame-next-scratch-length stack$c))
  :split-types t
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable nth-nontag)))
  :prepwork ((local
              (defthm stack$c-frame-next-scratchp-implies-natp-nth
                (implies (and (stack$c-frame-next-scratchp x)
                              (< (nfix n) (len x)))
                         (natp (nth n x)))
                :hints(("Goal" :in-theory (enable nth len)))
                :rule-classes (:rewrite (:type-prescription :typed-term (nth n x))))))
  (mbe :logic (non-exec (nth-nontag i (nth *stack$c-frame-next-scratchi1* stack$c)))
       :exec (stack$c-frame-next-scratchi1 i stack$c)))

(define stack$c-next-scratch ((stack$c))
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable nth-nontag)))
  (mbe :logic (nth-nontag *stack$c-next-scratch1* (non-exec stack$c))
       :exec (stack$c-next-scratch1 stack$c)))


(define stack$c-top-frame ((stack$c))
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable nth-nat)))
  (mbe :logic (nth-nat *stack$c-top-frame1* (non-exec stack$c))
       :exec (stack$c-top-frame1 stack$c)))

(local (fty::deffixequiv update-nth-array :args ((j natp) (acl2::key natp))))


(define update-stack$c-frame-top-minori ((i natp :type (integer 0 *))
                                         (val natp :type (integer 0 *))
                                         (stack$c))
  :guard (< i (stack$c-frame-top-minor-length stack$c))
  :split-types t
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable nth-nat unsigned-byte-p)))
  :prepwork ((local
              (defthm stack$c-frame-top-minorp-implies-natp-nth
                (implies (and (stack$c-frame-top-minorp x)
                              (< (nfix n) (len x)))
                         (natp (nth n x)))
                :hints(("Goal" :in-theory (enable nth len)))
                :rule-classes (:rewrite (:type-prescription :typed-term (nth n x))))))
  (mbe :logic (update-stack$c-frame-top-minori1 i (nfix val) stack$c)
       :exec (if (<= val #uxffff_ffff)
                 (update-stack$c-frame-top-minori1 i val stack$c)
               (ec-call (update-stack$c-frame-top-minori1 i val stack$c)))))

(define update-stack$c-top-minor ((val natp :type (integer 0 *))
                                  (stack$c))
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable nth-nat unsigned-byte-p)))
  (mbe :logic (update-stack$c-top-minor1 (nfix val) stack$c)
       :exec (if (<= val #uxffff_ffff)
                 (update-stack$c-top-minor1 val stack$c)
               (ec-call (update-stack$c-top-minor1 val stack$c)))))

(define update-stack$c-frame-next-scratchi ((i natp :type (integer 0 *))
                                         (val scratch-nontagidx-p :type (integer 0 *))
                                         (stack$c))
  :guard (< i (stack$c-frame-next-scratch-length stack$c))
  :split-types t
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable nth-nat unsigned-byte-p)))
  :prepwork ((local
              (defthm stack$c-frame-next-scratchp-implies-natp-nth
                (implies (and (stack$c-frame-next-scratchp x)
                              (< (nfix n) (len x)))
                         (natp (nth n x)))
                :hints(("Goal" :in-theory (enable nth len)))
                :rule-classes (:rewrite (:type-prescription :typed-term (nth n x))))))
  (mbe :logic (update-stack$c-frame-next-scratchi1 i (scratch-nontagidx-fix val) stack$c)
       :exec (if (<= val #uxffff_ffff)
                 (update-stack$c-frame-next-scratchi1 i val stack$c)
               (ec-call (update-stack$c-frame-next-scratchi1 i val stack$c)))))

(define update-stack$c-next-scratch ((val scratch-nontagidx-p :type (integer 0 *))
                                  (stack$c))
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable nth-nat unsigned-byte-p)))
  (mbe :logic (update-stack$c-next-scratch1 (scratch-nontagidx-fix val) stack$c)
       :exec (if (<= val #uxffff_ffff)
                 (update-stack$c-next-scratch1 val stack$c)
               (ec-call (update-stack$c-next-scratch1 val stack$c)))))


(define update-stack$c-top-frame ((val natp :type (integer 0 *))
                                  (stack$c))
  :enabled t
  :inline t
  :guard-hints (("goal" :in-theory (enable nth-nat unsigned-byte-p)))
  (mbe :logic (update-stack$c-top-frame1 (nfix val) stack$c)
       :exec (if (<= val #uxffff_ffff)
                 (update-stack$c-top-frame1 val stack$c)
               (ec-call (update-stack$c-top-frame1 val stack$c)))))








(defun-sk stack$c-minor-frames-welltyped (stack$c)
  (forall i
          (implies (and (natp i)
                        ;; (<= i (stack$c-top-minor stack$c))
                        )
                   (and (fgl-object-bindings-p (nth (* 3 i) (nth *stack$c-minori* stack$c)))
                        (pseudo-termp (nth (+ 1 (* 3 i)) (nth *stack$c-minori* stack$c)))
                        (acl2::maybe-natp (nth (+ 2 (* 3 i)) (nth *stack$c-minori* stack$c))))))
  :rewrite :direct)

(in-theory (disable stack$c-minor-frames-welltyped
                    stack$c-minor-frames-welltyped-necc))

(local (in-theory (enable stack$c-minor-frames-welltyped-necc)))

(local
 (defthm stack$c-minor-frames-welltyped-zero
   (implies (stack$c-minor-frames-welltyped stack$c)
            (and (fgl-object-bindings-p (nth 0 (nth *stack$c-minori* stack$c)))
                 (pseudo-termp (nth 1 (nth *stack$c-minori* stack$c)))
                 (acl2::maybe-natp (nth 2 (nth *stack$c-minori* stack$c)))))
   :hints (("goal" :use ((:instance stack$c-minor-frames-welltyped-necc (i 0)))))))

;; (defthm stack$c-minor-frames-welltyped-implies-fgl-object-bindings-p
;;   (implies (and (stack$c-minor-frames-welltyped stack$c)
;;                 (posp n) (<= n (stack$c-nframes stack$c)))
;;            (fgl-object-bindings-p (nth (+ -3 (* 3 n)) (nth *stack$c-minori* stack$c))))
;;   :hints (("goal" :use ((:instance stack$c-minor-frames-welltyped-necc (i (1- n))))
;;            :in-theory (disable stack$c-minor-frames-welltyped-necc))))

;; (defthm stack$c-minor-frames-welltyped-implies-fgl-objectlist-p
;;   (implies (and (stack$c-minor-frames-welltyped stack$c)
;;                 (posp n) (<= n (stack$c-nframes stack$c)))
;;            (fgl-objectlist-p (nth (+ -2 (* 3 n)) (nth *stack$c-minori* stack$c))))
;;   :hints (("goal" :use ((:instance stack$c-minor-frames-welltyped-necc (i (1- n))))
;;            :in-theory (disable stack$c-minor-frames-welltyped-necc))))

(defun-sk stack$c-major-frames-welltyped (stack$c)
  (forall i
          (implies (and (natp i)
                        ;; (<= i (stack$c-top-frame stack$c))
                        )
                   (and (fgl-object-bindings-p (nth (* 3 i) (nth *stack$c-majori* stack$c)))
                        (maybe-fgl-generic-rule-p (nth (+ 1 (* 3 i)) (nth *stack$c-majori* stack$c)))
                        (acl2::maybe-natp (nth (+ 2 (* 3 i)) (nth *stack$c-majori* stack$c))))))
  :rewrite :direct)

(in-theory (disable stack$c-major-frames-welltyped
                    stack$c-major-frames-welltyped-necc))

(local (in-theory (enable stack$c-major-frames-welltyped-necc)))

(local
 (defthm stack$c-major-frames-welltyped-zero
   (implies (stack$c-major-frames-welltyped stack$c)
            (and (fgl-object-bindings-p (nth 0 (nth *stack$c-majori* stack$c)))
                 (maybe-fgl-generic-rule-p (nth 1 (nth *stack$c-majori* stack$c)))
                 (acl2::maybe-natp (nth 2 (nth *stack$c-majori* stack$c)))))
   :hints (("goal" :use ((:instance stack$c-major-frames-welltyped-necc (i 0)))))))


(defun-sk stack$c-top-minor-ordered (limit stack$c)
  (forall (i j)
          (implies (and (natp i)
                        (integerp j)
                        (< i j)
                        (< j (nfix limit)))
                   (< (nth-nat i (nth *stack$c-frame-top-minori1* stack$c))
                      (nth-nat j (nth *stack$c-frame-top-minori1* stack$c)))))
  :rewrite :direct)

(in-theory (disable stack$c-top-minor-ordered
                    stack$c-top-minor-ordered-necc))

(local (in-theory (enable stack$c-top-minor-ordered-necc)))

(local
 (defthm stack$c-top-minor-ordered-lte
   (implies (and (stack$c-top-minor-ordered limit stack$c)
                 (natp i)
                 (integerp j)
                 (<= i j)
                 (< j (nfix limit)))
            (and (<= (nth-nat i (nth *stack$c-frame-top-minori1* stack$c))
                     (nth-nat j (nth *stack$c-frame-top-minori1* stack$c)))
                 (< (nth-nat i (nth *stack$c-frame-top-minori1* stack$c))
                    (+ 1 (nth-nat j (nth *stack$c-frame-top-minori1* stack$c))))))
   :hints (("goal" :use ((:instance stack$c-top-minor-ordered-necc))
            :in-theory (disable stack$c-top-minor-ordered-necc)))))

(local
 (defthm stack$c-top-minor-ordered-minus1
   (implies (and (stack$c-top-minor-ordered limit stack$c)
                 (posp i)
                 (< i (nfix limit)))
            (and (< (nth-nat (+ -1 i) (nth *stack$c-frame-top-minori1* stack$c))
                    (nth-nat i (nth *stack$c-frame-top-minori1* stack$c)))
                 (<= (+ 1 (nth-nat (+ -1 i) (nth *stack$c-frame-top-minori1* stack$c)))
                     (nth-nat i (nth *stack$c-frame-top-minori1* stack$c)))))
   :hints (("goal" :use ((:instance stack$c-top-minor-ordered-necc (i (+ -1 i)) (j i)))
            :in-theory (disable stack$c-top-minor-ordered-necc)))
   :rule-classes (:rewrite :linear)))

(local
 (defthm stack$c-top-minor-ordered-plus1
   (implies (and (stack$c-top-minor-ordered limit stack$c)
                 (natp i)
                 (< (+ 1 i) (nfix limit)))
            (and (< (nth-nat i (nth *stack$c-frame-top-minori1* stack$c))
                    (nth-nat (+ 1 i) (nth *stack$c-frame-top-minori1* stack$c)))
                 (<= (+ 1 (nth-nat i (nth *stack$c-frame-top-minori1* stack$c)))
                     (nth-nat (+ 1 i) (nth *stack$c-frame-top-minori1* stack$c)))))
   :hints (("goal" :use ((:instance stack$c-top-minor-ordered-necc (i i) (j (+ 1 i))))
            :in-theory (disable stack$c-top-minor-ordered-necc)))
   :rule-classes (:rewrite :linear)))

(local (defthm stack$c-top-minor-ordered-when-greater
         (implies (and (stack$c-top-minor-ordered limit1 stack$c)
                       (<= (nfix limit) (nfix limit1)))
                  (stack$c-top-minor-ordered limit stack$c))
         :hints ((and stable-under-simplificationp
                      `(:expand (,(car (last clause))))))))


(defun-sk stack$c-top-minor-bounded (limit stack$c)
  (forall (j)
          (implies (< (nfix j) (nfix limit))
                   (< (nth-nat j (nth *stack$c-frame-top-minori1* stack$c))
                      (nth-nat *stack$c-top-minor1* stack$c))))
  :rewrite :direct)

(in-theory (disable stack$c-top-minor-bounded
                    stack$c-top-minor-bounded-necc))

(local (in-theory (enable stack$c-top-minor-bounded-necc)))

(local (defthm stack$c-top-minor-bounded-linear
         (implies (and (stack$c-top-minor-bounded limit stack$c)
                       (< (nfix j) (nfix limit)))
                  (< (nth-nat j (nth *stack$c-frame-top-minori1* stack$c))
                     (nth-nat *stack$c-top-minor1* stack$c)))
         :rule-classes :linear))

(local (defthm stack$c-top-minor-bounded-when-greater
         (implies (and (stack$c-top-minor-bounded limit1 stack$c)
                       (<= (nfix limit) (nfix limit1)))
                  (stack$c-top-minor-bounded limit stack$c))
         :hints ((and stable-under-simplificationp
                      `(:expand (,(car (last clause))))))))


(local (defthm stack$c-top-minor-bounded-implies-lte
         (implies (and (stack$c-top-minor-bounded limit stack$c)
                       (< (nfix j) (nfix limit)))
                  (<= (nth-nat j (nth *stack$c-frame-top-minori1* stack$c))
                      (nth-nat *stack$c-top-minor1* stack$c)))))


(defun-sk stack$c-minor-frames-bounded (stack$c)
  (forall i
          (implies (<= (+ 3 (* 3 (stack$c-top-minor stack$c)))
                       (nfix i))
                   (equal (nth i (nth *stack$c-minori* stack$c)) nil)))
  :rewrite :direct)

;; (defun-sk stack$c-minor-frames-bounded (stack$c)
;;   (forall i
;;           (implies (and (< (stack$c-top-minor stack$c) i)
;;                         (integerp i))
;;                    (and (equal (nth (* 3 i) (nth *stack$c-minori* stack$c)) nil)
;;                         (equal (nth (+ 1 (* 3 i)) (nth *stack$c-minori* stack$c)) nil)
;;                         (equal (nth (+ 2 (* 3 i)) (nth *stack$c-minori* stack$c)) 0))))
;;   :rewrite :direct)

(in-theory (disable stack$c-minor-frames-bounded
                    stack$c-minor-frames-bounded-necc))

(local (in-theory (enable stack$c-minor-frames-bounded-necc)))

(defun-sk stack$c-major-frames-bounded (stack$c)
  (forall i
          (implies (<= (+ 3 (* 3 (stack$c-top-frame stack$c)))
                       (nfix i))
                   (equal (nth i (nth *stack$c-majori* stack$c)) nil)))
  :rewrite :direct)

;; (defun-sk stack$c-major-frames-bounded (stack$c)
;;   (forall i
;;           (implies (and (< (stack$c-top-frame stack$c) i)
;;                         (integerp i))
;;                    (and (equal (nth (* 3 i) (nth *stack$c-majori* stack$c)) nil)
;;                         (equal (nth (+ 1 (* 3 i)) (nth *stack$c-majori* stack$c))
;;                                (stack-default-rule))
;;                         (equal (nth (+ 2 (* 3 i)) (nth *stack$c-majori* stack$c)) 0))))
;;   :rewrite :direct)

(in-theory (disable stack$c-major-frames-bounded
                    stack$c-major-frames-bounded-necc))

(local (in-theory (enable stack$c-major-frames-bounded-necc)))

(defun-sk stack$c-next-scratch-ordered (limit stack$c)
  (forall (i j)
          (implies (and (natp i)
                        (integerp j)
                        (<= i j)
                        (< j (nfix limit)))
                   (<= (nth-nontag i (nth *stack$c-frame-next-scratchi1* stack$c))
                       (nth-nontag j (nth *stack$c-frame-next-scratchi1* stack$c)))))
  :rewrite :direct)

(in-theory (disable stack$c-next-scratch-ordered
                    stack$c-next-scratch-ordered-necc))

(local (in-theory (enable stack$c-next-scratch-ordered-necc)))



(local
 (defthmd stack$c-next-scratch-ordered-necc-split
   (implies (and (stack$c-next-scratch-ordered limit stack$c)
                 (natp i)
                 (integerp j)
                 (<= i j)
                 (case-split (< j (nfix limit))))
            (<= (nth-nontag i (nth *stack$c-frame-next-scratchi1* stack$c))
                (nth-nontag j (nth *stack$c-frame-next-scratchi1* stack$c))))))

(local
 (defthmd stack$c-next-scratch-ordered-necc-nfix
   (implies (and (stack$c-next-scratch-ordered limit stack$c)
                 (<= (nfix i) (nfix j))
                 (< (nfix j) (nfix limit)))
            (<= (nth-nontag i (nth *stack$c-frame-next-scratchi1* stack$c))
                (nth-nontag j (nth *stack$c-frame-next-scratchi1* stack$c))))
   :hints (("goal" :use ((:instance stack$c-next-scratch-ordered-necc
                          (i (nfix i)) (j (nfix j))))
            :in-theory (disable stack$c-next-scratch-ordered-necc)))))

(local (defthm stack$c-next-scratch-ordered-when-greater
         (implies (and (stack$c-next-scratch-ordered limit1 stack$c)
                       (<= (nfix limit) (nfix limit1)))
                  (stack$c-next-scratch-ordered limit stack$c))
         :hints ((and stable-under-simplificationp
                      `(:expand (,(car (last clause))))))))

(local
 (defthm stack$c-next-scratch-ordered-minus1
   (implies (and (stack$c-next-scratch-ordered limit stack$c)
                 (posp i)
                 (< i (nfix limit)))
            (<= (nth-nontag (+ -1 i) (nth *stack$c-frame-next-scratchi1* stack$c))
                (nth-nontag i (nth *stack$c-frame-next-scratchi1* stack$c))))
   :hints (("goal" :use ((:instance stack$c-next-scratch-ordered-necc (i (+ -1 i)) (j i)))
            :in-theory (disable stack$c-next-scratch-ordered-necc)))
   :rule-classes (:rewrite :linear)))

(local
 (defthm stack$c-next-scratch-ordered-plus1
   (implies (and (stack$c-next-scratch-ordered limit stack$c)
                 (natp i)
                 (< (+ 1 i) (nfix limit)))
            (<= (nth-nontag i (nth *stack$c-frame-next-scratchi1* stack$c))
                (nth-nontag (+ 1 i) (nth *stack$c-frame-next-scratchi1* stack$c))))
   :hints (("goal" :use ((:instance stack$c-next-scratch-ordered-necc (i i) (j (+ 1 i))))
            :in-theory (disable stack$c-next-scratch-ordered-necc)))
   :rule-classes (:rewrite :linear)))

(defun-sk stack$c-next-scratch-bounded (limit stack$c)
  (forall (j)
          (implies (< (nfix j) (nfix limit))
                   (<= (nth-nontag j (nth *stack$c-frame-next-scratchi1* stack$c))
                       (nth-nontag *stack$c-next-scratch1* stack$c))))
  :rewrite :direct)

(in-theory (disable stack$c-next-scratch-bounded
                    stack$c-next-scratch-bounded-necc))

(local (in-theory (enable stack$c-next-scratch-bounded-necc)))

(local
 (defthm stack$c-next-scratch-bounded-linear
   (implies (and (stack$c-next-scratch-bounded limit stack$c)
                 (< (nfix j) (nfix limit)))
            (<= (nth-nontag j (nth *stack$c-frame-next-scratchi1* stack$c))
                (nth-nontag *stack$c-next-scratch1* stack$c)))
   :rule-classes :linear))

(local
 (defthm stack$c-next-scratch-bounded-when-greater
   (implies (and (stack$c-next-scratch-bounded limit1 stack$c)
                 (<= (nfix limit) (nfix limit1)))
            (stack$c-next-scratch-bounded limit stack$c))
   :hints ((and stable-under-simplificationp
                `(:expand (,(car (last clause))))))))



(defun-sk stack$c-scratch-codeslots-ok (stack$c)
  (forall i
          (implies (and (equal (loghead 4 (nfix i)) 0)
                        ;; NOTE: no need for bounds here since initially all indices will have value 0
                        ;; (< (nfix i) (stack$c-next-scratch stack$c))
                        )
                   (unsigned-byte-p 60 (nth-scratch i (nth *stack$c-scratchi1* stack$c)))))
  :rewrite :direct)

(in-theory (disable stack$c-scratch-codeslots-ok
                    stack$c-scratch-codeslots-ok-necc))


(local (defthm stack$c-scratch-codeslots-ok-implies
         (implies (and (stack$c-scratch-codeslots-ok stack$c)
                       (equal (loghead 4 (nfix i)) 0)
                       ;; (< (nfix i) (stack$c-next-scratch stack$c))
                       )
                  (and (integerp (nth-scratch i (nth *stack$c-scratchi1* stack$c)))
                       (natp (nth-scratch i (nth *stack$c-scratchi1* stack$c)))
                       (unsigned-byte-p 60 (nth-scratch i (nth *stack$c-scratchi1* stack$c)))))
         :hints (("goal" :use stack$c-scratch-codeslots-ok-necc))))

(local (defthm stack$c-scratch-codeslots-ok-of-update-nontagidx
         (implies (and (stack$c-scratch-codeslots-ok stack$c)
                       (scratch-nontagidx-p n))
                  (stack$c-scratch-codeslots-ok
                   (update-nth-scratch-array *stack$c-scratchi1* n val stack$c)))
         :hints ((and stable-under-simplificationp
                      `(:expand (,(car (last clause))))))))




(local (defthm logsquash-is-ash-of-logtail
         (implies (natp n)
                  (equal (ash (logtail n x) n)
                         (bitops::logsquash n x)))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))

(define stack$c-bounds-ok (stack$c)
  :enabled t
  (and (<= (+ 3 (* 3 (stack$c-top-frame stack$c))) (stack$c-major-length stack$c))
       (<= (stack$c-top-frame stack$c) (stack$c-frame-top-minor-length stack$c))
       (<= (+ 3 (* 3 (stack$c-top-minor stack$c)))
           (stack$c-minor-length stack$c))
       (<= (stack$c-top-minor stack$c)
           (stack$c-frame-next-scratch-length stack$c))
       (< (stack$c-next-scratch stack$c)
          (stack$c-scratch-length stack$c))))




(define scratch-codeslot ((tail natp :type (unsigned-byte 32))
                          (stack$c stack$c-bounds-ok))
  :guard (and (< (ash tail 4) (stack$c-next-scratch stack$c))
              (ec-call (stack$c-scratch-codeslots-ok stack$c)))
  :returns (codeslot-val natp :rule-classes :type-prescription)
  :prepwork ()
  (loghead 60 (stack$c-scratchi (ash (nfix tail) 4) stack$c))
  ///
  (defret unsigned-byte-60-of-<fn>
    (unsigned-byte-p 60 codeslot-val))

  (defret scratch-codeslot-of-update-stack$c-scratchi
    (implies (not (equal 0 (loghead 4 (nfix m))))
             (equal (scratch-codeslot n (update-nth-scratch-array *stack$c-scratchi1* m v stack$c))
                    (scratch-codeslot n stack$c))))

  (def-updater-independence-thm scratch-codeslot-updater-independence
    (implies (equal (nth-scratch (ash (nfix tail) 4) (nth *stack$c-scratchi1* new))
                    (nth-scratch (ash (nfix tail) 4) (nth *stack$c-scratchi1* old)))
             (equal (scratch-codeslot tail new)
                    (scratch-codeslot tail old)))))

(local (defthm logand-less-when-inverse-not-equal-0
         (implies (and (syntaxp (quotep mask))
                       (natp x)
                       (not (equal 0 (logand (lognot mask) x))))
                  (< (logand mask x) x))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))
         :rule-classes :linear))

(local (defthm logand-less-than-other-when-inverse-not-equal-0
         (implies (and (syntaxp (quotep mask))
                       (natp x)
                       (<= x y)
                       (integerp y)
                       (not (equal 0 (logand (lognot mask) y))))
                  (< (logand mask x) y))
         :hints (("goal" :use ((:instance logand-less-when-inverse-not-equal-0))
                  :in-theory (disable logand-less-when-inverse-not-equal-0)))
         :rule-classes :linear))

(local (defthm unsigned-byte-p-when-less-than-nth-nontag
         (implies (and (<= n (nth-nontag i stack))
                       (natp n)
                       (unsigned-byte-p w (nth i stack))
                       (posp w))
                  (unsigned-byte-p w n))
         :hints (("goal" :use ((:instance unsigned-byte-p-of-nth-nontag
                                (k w) (n i) (x stack)))
                  :in-theory (e/d (unsigned-byte-p) (unsigned-byte-p-of-nth-nontag))))))

(define scratch-entry-codeslot ((n natp :type (unsigned-byte 32))
                                (stack$c stack$c-bounds-ok))
  :guard (and (<= n (stack$c-next-scratch stack$c))
              (ec-call (stack$c-scratch-codeslots-ok stack$c)))
  :returns (codeslot-val natp :rule-classes :type-prescription)
  :split-types t
  :inline t
  :enabled t
  :guard-hints (("goal" :in-theory (enable scratch-codeslot))
                (and stable-under-simplificationp
                     '(:in-theory (e/d (bitops::logsquash)
                                       (bitops::logand-with-negated-bitmask)))))
  (mbe :logic (scratch-codeslot (logtail 4 (nfix n)) stack$c)
       :exec (stack$c-scratchi (the (unsigned-byte 32) (logand #x-10 (the (unsigned-byte 32) n)))
                               stack$c)))

(define scratch-codeslot-code ((n :type (unsigned-byte 4))
                               (codeslot :type (unsigned-byte 60)))
  :guard (not (eql 0 n))
  :returns (code natp :rule-classes :type-prescription)
  (logand #xf
          (the (unsigned-byte 60)
               (ash (the (unsigned-byte 60) codeslot)
                    (- (the (unsigned-byte 6)
                            (ash (the (unsigned-byte 4)
                                      (+ -1
                                         (the (unsigned-byte 4)
                                              (mbe :logic (lposfix (loghead 4 n))
                                                   :exec n))))
                                 2))))))
  ///
  (defret unsigned-byte-4-of-<fn>
    (unsigned-byte-p 4 code)))


(define scratch-entry-kindcode ((n natp :type (unsigned-byte 32))
                                (stack$c stack$c-bounds-ok))
  :guard (and (<= n (stack$c-next-scratch stack$c))
              (not (eql 0 (loghead 4 n)))
              (ec-call (stack$c-scratch-codeslots-ok stack$c)))
  :split-types t
  :inline t
  :returns (code natp :rule-classes :type-prescription)
  (scratch-codeslot-code (the (unsigned-byte 4) (logand #xf (lnfix n)))
                         (scratch-entry-codeslot n stack$c))
  ///
  (defret unsigned-byte-4-of-<fn>
    (unsigned-byte-p 4 code))

  (defret scratch-entry-kindcode-of-update-stack$c-scratchi
    (implies (not (equal 0 (loghead 4 (nfix m))))
             (equal (scratch-entry-kindcode n (update-nth-scratch-array *stack$c-scratchi1* m v stack$c))
                    (scratch-entry-kindcode n stack$c))))

  (def-updater-independence-thm scratch-entry-kindcode-updater-independence
    (implies (equal (nth-scratch (logand #x-10 (nfix n)) (nth *stack$c-scratchi1* new))
                    (nth-scratch (logand #x-10 (nfix n)) (nth *stack$c-scratchi1* old)))
             (equal (scratch-entry-kindcode n new)
                    (scratch-entry-kindcode n old)))
    :hints(("Goal" :in-theory (enable logsquash-is-ash-of-logtail bitops::logsquash)))))


(make-event
 `(progn
    (define scratchobj-code/val-okp ((code natp) (val))
      (case (lnfix code)
        . ,(acl2::template-proj
            '(<codecase> (:@ (not :no-pred) (<pred> val))
                         (:@ :no-pred t))
            *scratchobj-tmplsubsts*))
      ///
      . ,(acl2::template-proj
          '(defthm scratchobj-code/val-okp-of-<kind>
             (:@ (not :no-pred)
              (implies (<pred> val)
                       (scratchobj-code/val-okp <code> val)))
             (:@ :no-pred
              (scratchobj-code/val-okp <code> val)))
          *scratchobj-tmplsubsts*))

    (define code/val->scratchobj ((code natp) (val))
      :guard (scratchobj-code/val-okp code val)
      :guard-hints (("goal" :in-theory (enable scratchobj-code/val-okp)))
      :returns (obj scratchobj-p)
      (scratchobj-fix
       (case (lnfix code)
         . ,(acl2::template-proj
             '(<codecase> (scratchobj-<kind> val))
             *scratchobj-tmplsubsts*)))
      ///
      ,@(acl2::template-proj
         '(defthm scratchobj-<kind>->val-of-code/val->scratchobj
            (equal (scratchobj-<kind>->val
                    (code/val->scratchobj <code> val))
                   (:@ (not :no-pred) (<fix> val))
                   (:@ :no-pred val)))
         *scratchobj-tmplsubsts*)

      ,@(acl2::template-proj
         '(defret scratchobj-<kind>->val-of-code/val->scratchobj-by-kind
            (implies (equal (scratchobj-code->kind code) :<kind>)
                     (equal (scratchobj-<kind>->val obj)
                            (:@ (not :no-pred) (<fix> val))
                            (:@ :no-pred val)))
            :hints(("Goal" :in-theory (enable scratchobj-code->kind))))
         *scratchobj-tmplsubsts*)

      (defret scratchobj-kind-of-<fn>
        (equal (scratchobj-kind obj)
               (scratchobj-code->kind code))
        :hints(("Goal" :in-theory (enable scratchobj-code->kind)))))

    (define scratchobj->val ((x scratchobj-p))
      :returns (val)
      (scratchobj-case x
        . ,(acl2::template-append
            '(:<kind> x.val)
            *scratchobj-tmplsubsts*))
      ///
      (defthm scratchobj-code/val-okp-of-scratchobj->val
        (scratchobj-code/val-okp (scratchobj-kind->code (scratchobj-kind obj))
                                 (scratchobj->val obj))
        :hints(("Goal" :in-theory (enable scratchobj-kind->code
                                          scratchobj-code/val-okp))))

      (defthm code/val->scratchobj-of-scratchobj->val
        (equal (code/val->scratchobj (scratchobj-kind->code (scratchobj-kind obj))
                                     (scratchobj->val obj))
               (scratchobj-fix obj))
        :hints(("Goal" :in-theory (enable scratchobj-kind->code
                                          code/val->scratchobj))))

      ,@(acl2::template-proj
         '(defthm scratchobj->val-of-scratchobj-<kind>
            (equal (scratchobj->val (scratchobj-<kind> val))
                   (:@ (not :no-pred) (<fix> val))
                   (:@ :no-pred val)))
         *scratchobj-tmplsubsts*))))

;; (define stack$c-bounds-ok (stack$c)
;;   :enabled t


(defun-sk stack$c-scratch-welltyped (stack$c)
  (forall i
          (implies (and (scratch-nontagidx-p i)
                        (< i (stack$c-next-scratch stack$c)))
                   (let ((code (scratch-entry-kindcode i stack$c))
                         (entry (nth-scratch i (nth *stack$c-scratchi1* stack$c))))
                     (scratchobj-code/val-okp code entry))))
  :rewrite :direct)

(in-theory (disable stack$c-scratch-welltyped
                    stack$c-scratch-welltyped-necc))

(local (in-theory (enable stack$c-scratch-welltyped-necc)))

(defthmd stack$c-scratch-welltyped-casesplit
  (implies (and (stack$c-scratch-welltyped stack$c)
                (scratch-nontagidx-p i)
                (case-split (< i (stack$c-next-scratch stack$c))))
           (let ((code (scratch-entry-kindcode i stack$c))
                 (entry (nth-scratch i (nth *stack$c-scratchi1* stack$c))))
             (scratchobj-code/val-okp code entry))))

(make-event
 (cons 'progn
       (acl2::template-append
        '((:@ (not :no-pred)
           (defthm stack$c-scratch-welltyped-implies-<kind>
             (implies (and (stack$c-scratch-welltyped stack$c)
                           (scratch-nontagidx-p i)
                           (< i (stack$c-next-scratch stack$c)))
                      (let ((code (scratch-entry-kindcode i stack$c))
                            (entry (nth-scratch i (nth *stack$c-scratchi1* stack$c))))
                        (implies (equal (scratchobj-code->kind code) :<kind>)
                                 (<pred> entry))))
             :hints (("goal" :use stack$c-scratch-welltyped-necc
                      :in-theory (e/d (scratchobj-code/val-okp
                                       scratchobj-code->kind)
                                      (stack$c-scratch-welltyped-necc)))))))
        *scratchobj-tmplsubsts*)))



(define stack$c-okp (stack$c)
  :enabled t
  (and (stack$c-bounds-ok stack$c)
       (ec-call (stack$c-top-minor-ordered (stack$c-top-frame stack$c) stack$c))
       (ec-call (stack$c-top-minor-bounded (stack$c-top-frame stack$c) stack$c))
       (ec-call (stack$c-next-scratch-ordered (stack$c-top-minor stack$c) stack$c))
       (ec-call (stack$c-next-scratch-bounded (stack$c-top-minor stack$c) stack$c))
       (ec-call (stack$c-major-frames-welltyped stack$c))
       (ec-call (stack$c-minor-frames-welltyped stack$c))
       (ec-call (stack$c-major-frames-bounded stack$c))
       (ec-call (stack$c-minor-frames-bounded stack$c))
       (ec-call (stack$c-scratch-codeslots-ok stack$c))
       (ec-call (stack$c-scratch-welltyped stack$c))))

(local (defthm scatchobj-code->kind-is-cinstlist-when-not-others
         (implies (and (not (equal (nfix x) 0))
                       (not (equal (nfix x) 1))
                       (not (equal (nfix x) 2))
                       (not (equal (nfix x) 3))
                       (not (equal (nfix x) 4)))
                  (equal (scratchobj-code->kind x) :cinstlist))
         :hints(("Goal" :in-theory (enable scratchobj-code->kind)))))



(local
 (progn
   (stobjs::def-range-equiv range-nth-nat-equiv :nth nth-nat)
   (stobjs::def-range-equiv range-nth-nontag-equiv :nth nth-nontag)
   ;; (stobjs::def-range-equiv range-nth-scratch-equiv :nth nth-scratch :update update-nth-scratch)
   ))


(make-event
 `(define stack$c-scratch-entry ((n scratch-nontagidx-p)
                                 (stack$c stack$c-okp))
    :guard (< n (stack$c-next-scratch stack$c))
    :returns (obj scratchobj-p)
    (b* ((n (scratch-nontagidx-fix n))
         (code (scratch-entry-kindcode n stack$c))
         (val (stack$c-scratchi n stack$c)))
      (code/val->scratchobj code val))
    ///
    ;; (defthm stack$c-scratch-entry-of-update-nth-scratch
    ;;   (implies (and (scratch-nontagidx-p m)
    ;;                 (not (equal m (scratch-nontagidx-fix n))))
    ;;            (equal (stack$c-scratch-entry n (update-nth-scratch-array *stack$c-scratchi1* m v stack$c))
    ;;                   (stack$c-scratch-entry n stack$c))))

    (def-updater-independence-thm stack$c-scratch-entry-updater-independence
      (implies (and (equal (scratch-entry-kindcode (scratch-nontagidx-fix n) new)
                           (scratch-entry-kindcode (scratch-nontagidx-fix n) old))
                    (equal (stack$c-scratchi (scratch-nontagidx-fix n) new)
                           (stack$c-scratchi (scratch-nontagidx-fix n) old)))
               (equal (stack$c-scratch-entry n new)
                      (stack$c-scratch-entry n old))))))




(local
 (defsection range-scratch-entry-equiv
   (defun-sk range-scratch-entry-equiv (min max x y)
     (forall i
             (implies (and (<= (scratch-nontagidx-fix min) (scratch-nontagidx-fix i))
                           (< (scratch-nontagidx-fix i) (scratch-nontagidx-fix max)))
                      (equal (stack$c-scratch-entry i x)
                             (stack$c-scratch-entry i y))))
     :rewrite :direct)
   
   (in-theory (disable range-scratch-entry-equiv
                       range-scratch-entry-equiv-necc))

   (defthm range-scratch-entry-equiv-self
     (range-scratch-entry-equiv min max x x)
     :hints(("Goal" :in-theory (enable range-scratch-entry-equiv))))

   (defthm range-stack-equiv-entry-when-superrange
     (implies (and (range-scratch-entry-equiv min1 max1 x y)
                   (<= (scratch-nontagidx-fix min1) (scratch-nontagidx-fix min))
                   (<= (scratch-nontagidx-fix max) (scratch-nontagidx-fix max1)))
              (range-scratch-entry-equiv min max x y))
     :hints ((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))
                    :in-theory (enable range-scratch-entry-equiv-necc)))))

   ;; update-kindcode isn't defined yet, prove similar about those later

   (fty::deffixequiv range-scratch-entry-equiv :args ((min scratch-nontagidx-p)
                                                    (max scratch-nontagidx-p))
     :hints ((and stable-under-simplificationp
                  (let ((lit (assoc 'range-scratch-entry-equiv clause)))
                    `(:expand (,lit)
                      :in-theory (enable range-scratch-entry-equiv-necc))))))

   (defthm range-scratch-entry-equiv-of-empty
     (implies (<= (scratch-nontagidx-fix max) (scratch-nontagidx-fix min))
              (range-scratch-entry-equiv min max x y))
     :hints(("Goal" :in-theory (enable range-scratch-entry-equiv))))

   (define range-scratch-entry-equiv-badguy (min max x y)
     :returns (badguy scratch-nontagidx-p
                      :hints(("Goal" :in-theory (enable range-scratch-entry-equiv)))
                      :rule-classes (:rewrite (:type-prescription :typed-term badguy)))
     :verify-guards nil
     (if (range-scratch-entry-equiv min max x y)
         (scratch-nontagidx-fix min)
       (scratch-nontagidx-fix (range-scratch-entry-equiv-witness min max x y)))
     ///     
     (local (in-theory (enable range-scratch-entry-equiv)))

     (defret range-scratch-entry-equiv-badguy-lower-bound
       (<= (scratch-nontagidx-fix min) badguy)
       :rule-classes :linear)

     (defret range-scratch-entry-equiv-badguy-lower-bound-rewrite
       (implies (<= min1 (scratch-nontagidx-fix min))
                (<= min1 badguy)))

     (defret range-scratch-entry-equiv-badguy-lower-bound-rewrite-less
       (implies (< min1 (scratch-nontagidx-fix min))
                (< min1 badguy)))

     (defret range-scratch-entry-equiv-badguy-lower-bound-rewrite-not-equal
       (implies (< min1 (scratch-nontagidx-fix min))
                (not (equal min1 badguy))))
     
     (defret range-scratch-entry-equiv-badguy-upper-bound
       (implies (< (scratch-nontagidx-fix min) (scratch-nontagidx-fix max))
                (< badguy (scratch-nontagidx-fix max)))
       :rule-classes :linear)

     (defret range-scratch-entry-equiv-badguy-upper-bound-rewrite-lte
       (implies (and (<= (scratch-nontagidx-fix max) max1)
                     (<= (scratch-nontagidx-fix min) (scratch-nontagidx-fix max)))
                (<= badguy max1)))

     (defret range-scratch-entry-equiv-badguy-upper-bound-rewrite-less
       (implies (and (<= (scratch-nontagidx-fix max) max1)
                     (< (scratch-nontagidx-fix min) (scratch-nontagidx-fix max)))
                (< badguy max1)))

     (defret range-scratch-entry-equiv-badguy-upper-bound-rewrite-not-equal
       (implies (and (<= (scratch-nontagidx-fix max) max1)
                     (< (scratch-nontagidx-fix min) (scratch-nontagidx-fix max)))
                (not (equal badguy max1))))

     (defret range-scratch-entry-equiv-badguy-upper-bound-when-not-equiv
       (implies (not (range-scratch-entry-equiv min max x y))
                (< badguy (scratch-nontagidx-fix max)))
       :rule-classes ((:linear :backchain-limit-lst 0)))

     (defret range-scratch-entry-equiv-badguy-upper-bound-when-not-equiv-rewrite-lte
       (implies (and (not (range-scratch-entry-equiv min max x y))
                     (<= (scratch-nontagidx-fix max) max1))
                (<= badguy max1))
       :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

     (defret range-scratch-entry-equiv-badguy-upper-bound-when-not-equiv-rewrite-less
       (implies (and (not (range-scratch-entry-equiv min max x y))
                     (<= (scratch-nontagidx-fix max) max1))
                (< badguy max1))
       :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

     (defret range-scratch-entry-equiv-badguy-upper-bound-when-not-equiv-rewrite-not-equal
       (implies (and (not (range-scratch-entry-equiv min max x y))
                     (<= (scratch-nontagidx-fix max) max1))
                (not (equal badguy max1)))
       :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

     (defret range-scratch-entry-equiv-by-badguy
       (implies (equal (stack$c-scratch-entry badguy x)
                       (stack$c-scratch-entry badguy y))
                (range-scratch-entry-equiv min max x y)))

     (local (defthm range-scratch-entry-equiv-by-witness
              (let ((badguy (range-scratch-entry-equiv-witness min max x y)))
                (implies (equal (stack$c-scratch-entry badguy x)
                                (stack$c-scratch-entry badguy y))
                         (range-scratch-entry-equiv min max x y)))))

     (defret range-scratch-entry-equiv-by-badguy-literal
       (implies (acl2::rewriting-positive-literal `(range-scratch-entry-equiv ,min ,max ,x ,y))
                (iff (range-scratch-entry-equiv min max x y)
                     (or (<= (scratch-nontagidx-fix max) (scratch-nontagidx-fix min))
                         (equal (stack$c-scratch-entry badguy x)
                                (stack$c-scratch-entry badguy y)))))
       :hints(("Goal" :in-theory (e/d (range-scratch-entry-equiv-necc)
                                      (range-scratch-entry-equiv))))))

   
   
   (defthm range-scratch-entry-equiv-of-update-nth-scratch-out-of-range-2
     (implies (and (scratch-nontagidx-p i)
                   (not (and (<= (scratch-nontagidx-fix min) i)
                             (< i (scratch-nontagidx-fix max)))))
              (iff (range-scratch-entry-equiv min max x (update-nth-scratch-array *stack$c-scratchi1* i v y))
                   (range-scratch-entry-equiv min max x y)))
     :hints(("Goal" :in-theory (enable range-scratch-entry-equiv-necc))))

   (defthm range-scratch-entry-equiv-of-update-nth-scratch-array-out-of-range-1
     (implies (and (scratch-nontagidx-p i)
                   (not (and (<= (scratch-nontagidx-fix min) i)
                             (< i (scratch-nontagidx-fix max)))))
              (iff (range-scratch-entry-equiv min max (update-nth-scratch-array *stack$c-scratchi1* i v x) y)
                   (range-scratch-entry-equiv min max x y)))
     :hints (("Goal" :in-theory (enable range-scratch-entry-equiv-necc))
             (and stable-under-simplificationp
                  '(:use ((:instance range-scratch-entry-equiv-necc
                           (x (update-nth-scratch-array *stack$c-scratchi1* i v x))
                           (i (range-scratch-entry-equiv-badguy min max x y))))
                    :in-theory (disable range-scratch-entry-equiv-necc)))))

   (defthm range-scratch-entry-equiv-when-range-scratch-entry-equiv
     (implies (range-scratch-entry-equiv min max x y)
              (range-scratch-entry-equiv min max x y)))

   (defthmd range-scratch-entry-equiv-commute
     (implies (range-scratch-entry-equiv min max y x)
              (range-scratch-entry-equiv min max x y))
     :hints(("Goal" :in-theory (enable range-scratch-entry-equiv-necc))))))
   




;; (local
;;  (def-updater-independence-thm stack$c-scratch-entry-of-update
;;    (implies (and (equal nn (scratch-nontagidx-fix n))
;;                  (equal (scratch-entry-kindcode nn new)
;;                         (scratch-entry-kindcode nn old))
;;                  (equal (stack$c-scratchi nn new)
;;                         (stack$c-scratchi nn old)))
;;             (equal (stack$c-scratch-entry n new)
;;                    (stack$c-scratch-entry n old)))
;;    :hints(("Goal" :in-theory (enable stack$c-scratch-entry)))))


(define stack$c-build-scratch ((bottom scratch-nontagidx-p)
                               (next scratch-nontagidx-p)
                               (stack$c stack$c-okp))
  :returns (scratch scratchlist-p)
  :guard (and (<= bottom next)
              (<= next (stack$c-next-scratch stack$c)))
  :measure (nfix (- (scratch-nontagidx-fix next) (scratch-nontagidx-fix bottom)))
  :prepwork ((local (in-theory (disable scratch-decr-nontagidx-in-terms-of-conversions))))
  (b* ((next (scratch-nontagidx-fix next))
       (bottom (scratch-nontagidx-fix bottom))
       ((when (mbe :logic (zp (- next bottom))
                   :exec (int= bottom next)))
        nil)
       (top (scratch-decr-nontagidx next)))
    (cons (stack$c-scratch-entry top stack$c)
          (stack$c-build-scratch bottom top stack$c)))
  ///

  (local (defthm scratch-nontagidx-to-index-monotonic-linear-1
           (implies (and (equal xx (scratch-nontagidx-fix x))
                         (< xx y)
                         (scratch-nontagidx-p y))
                    (< (scratch-nontagidx-to-index x) (scratch-nontagidx-to-index y)))
           :rule-classes :linear))

  (local (defthm scratch-nontagidx-to-index-monotonic-linear-2
           (implies (and (equal xx (scratch-nontagidx-fix x))
                         (> xx y)
                         (scratch-nontagidx-p y))
                    (> (scratch-nontagidx-to-index x) (scratch-nontagidx-to-index y)))
           :rule-classes :linear))

  (defret len-of-<fn>
    (equal (len scratch)
           (nfix
            (- (scratch-nontagidx-to-index next)
               (scratch-nontagidx-to-index bottom))))
    :hints(("Goal" :in-theory (enable len scratch-decr-nontagidx-in-terms-of-conversions))))

  (defthm stack$c-build-scratch-of-same
    (equal (stack$c-build-scratch top top stack$c)
           nil))


  (local (defun nth-of-stack$c-build-scratch-ind (n bottom next stack$c)
           (declare (xargs :measure (nfix n)))
           (b* ((next (scratch-nontagidx-fix next))
                (bottom (scratch-nontagidx-fix bottom))
                ((when (or (zp n)
                           (mbe :logic (zp (- next bottom))
                                :exec (int= bottom next))))
                 stack$c)
                (top (scratch-decr-nontagidx next)))
             (nth-of-stack$c-build-scratch-ind (1- n) bottom top stack$c))))
           
  (local (defthm scratch-nontagidx-equiv-when-fixes-equal
           (implies (equal (scratch-nontagidx-fix x) (scratch-nontagidx-fix y))
                    (scratch-nontagidx-equiv x y))
           :rule-classes :forward-chaining))
  

  (defret nth-of-stack$c-build-scratch
    (implies (< (nfix n) (len scratch))
             (equal (nth n scratch)
                    (stack$c-scratch-entry
                     (index-to-scratch-nontagidx (- (scratch-nontagidx-to-index next) (+ 1 (nfix n))))
                     stack$c)))
    :hints(("Goal" :in-theory (enable scratch-decr-nontagidx-in-terms-of-conversions)
            :induct (nth-of-stack$c-build-scratch-ind n bottom next stack$c)
            :expand ((:free (a b) (nth n (cons a b))))))))



(local
 (defsection stack$c-build-scratch-of-update
   (local (defthm scratch-nontagidx-to-index-monotonic-linear-1
            (implies (and (equal xx (scratch-nontagidx-fix x))
                          (< xx y)
                          (scratch-nontagidx-p y))
                     (< (scratch-nontagidx-to-index x) (scratch-nontagidx-to-index y)))
            :rule-classes :linear))

   (local (defthm scratch-nontagidx-to-index-monotonic-linear-2
            (implies (and (equal xx (scratch-nontagidx-fix x))
                          (> xx y)
                          (scratch-nontagidx-p y))
                     (> (scratch-nontagidx-to-index x) (scratch-nontagidx-to-index y)))
            :rule-classes :linear))

   (local (defthm hack
            (implies (posp x)
                     (<= (nfix (+ -2 x)) (+ -1 x)))
            :hints(("Goal" :in-theory (enable nfix)))))

   (def-updater-independence-thm stack$c-build-scratch-of-update
     (implies (range-scratch-entry-equiv bottom
                                         top
                                         new
                                         old)
              (equal (stack$c-build-scratch bottom top new)
                     (stack$c-build-scratch bottom top old)))
     :hints (("goal" :induct (stack$c-build-scratch bottom top new)
              
              :expand ((:free (new) (stack$c-build-scratch bottom top new)))
              :in-theory (e/d (range-scratch-entry-equiv-necc
                               (:i stack$c-build-scratch))
                              (range-scratch-entry-equiv-by-badguy-literal
                               scratch-decr-nontagidx-in-terms-of-conversions)))))))


(define stack$c-build-minor-frame ((n natp)
                                   (next-scratch scratch-nontagidx-p)
                                   (stack$c stack$c-okp))
  :guard (and (<= n (stack$c-top-minor stack$c))
              (<= (if (eql (lnfix n) 0)
                      1
                    (stack$c-frame-next-scratchi (1- n) stack$c))
                  next-scratch)
              (<= next-scratch (stack$c-next-scratch stack$c)))
  :returns (frame minor-frame-p)
  :guard-debug t
  :guard-hints (("goal" :do-not-induct t))
  (make-minor-frame :bindings (stack$c-minori (* 3 (lnfix n)) stack$c)
                    :scratch
                    (b* ((prev-next (if (eql (lnfix n) 0)
                                        1
                                      (stack$c-frame-next-scratchi (1- n) stack$c))))
                      (stack$c-build-scratch prev-next next-scratch stack$c))
                    :term (stack$c-minori (+ 1 (* 3 (lnfix n))) stack$c)
                    :term-index (stack$c-minori (+ 2 (* 3 (lnfix n))) stack$c))

  ///
  (defret scratch-len-of-<fn>
    ;(implies (stack$c-okp stack$c)
    (equal (len (minor-frame->scratch frame))
           (nfix
            (- (scratch-nontagidx-to-index next-scratch)
               (scratch-nontagidx-to-index (if (zp n)
                                               1
                                             (stack$c-frame-next-scratchi
                                              (1- n) stack$c)))))))

  (defret nth-scratch-of-<fn>
    (implies (< (nfix k) (len (minor-frame->scratch frame)))
             (equal (nth k (minor-frame->scratch frame))
                    (stack$c-scratch-entry
                     (index-to-scratch-nontagidx (- (scratch-nontagidx-to-index next-scratch) (+ 1 (nfix k))))
                     stack$c)))))


(local
 (def-updater-independence-thm stack$c-build-minor-frame-of-update
   (implies (and (implies (posp n)
                          (equal (stack$c-frame-next-scratchi (1- n) new)
                                 (stack$c-frame-next-scratchi (1- n) old)))
                 (range-scratch-entry-equiv 1
                                            next-scratch
                                            new old)
                 (stobjs::range-equal-min-max (* 3 (nfix n))
                                              (+ 2 (* 3 (nfix n)))
                                              (nth *stack$c-minori* new)
                                              (nth *stack$c-minori* old)))
            (equal (stack$c-build-minor-frame n next-scratch new)
                   (stack$c-build-minor-frame n next-scratch old)))
   :hints(("Goal" :in-theory (e/d (stack$c-build-minor-frame
                                     stobjs::nth-when-range-equal-min-max)
                                  (scratch-decr-nontagidx-in-terms-of-conversions))))))


(define stack$c-build-minor-frames ((bottom natp) (top natp) (stack$c stack$c-okp))
  :returns (frames minor-stack-p)
  :measure (lnfix top)
  :ruler-extenders (cons)
  :guard (< top (stack$c-top-minor stack$c))
  :guard-debug t
  :guard-hints (("goal" :do-not-induct t))
  (cons (stack$c-build-minor-frame top (stack$c-frame-next-scratchi top stack$c) stack$c)
        (and (< (lnfix bottom) (lnfix top))
             (stack$c-build-minor-frames bottom (1- (lnfix top)) stack$c)))
  ///
  (defthm len-of-stack$c-build-minor-frames
    (equal (len (stack$c-build-minor-frames bottom top stack$c))
           (pos-fix (+ 1 (- (nfix top) (nfix bottom)))))
    :hints(("Goal" :in-theory (enable len pos-fix))))

  (local (defun nth-ind (n top bottom)
           (if (<= (lnfix top) (lnfix bottom))
               n
             (nth-ind (+ -1 (nfix n)) (+ -1 top) bottom))))

  (defthm nth-of-stack$c-build-minor-frames
    (implies (<= (nfix n) (- (nfix top) (nfix bottom)))
             (equal (nth n (stack$c-build-minor-frames bottom top stack$c))
                    (stack$c-build-minor-frame (- (nfix top) (nfix n))
                                               (stack$c-frame-next-scratchi
                                                (- (nfix top) (nfix n)) stack$c)
                                               stack$c)))
    :hints(("Goal" :induct (nth-ind n top bottom)
            :expand ((:free (a b) (nth n (cons a b)))
                     (stack$c-build-minor-frames bottom top stack$c)))))

  (defret minor-stack-scratch-len-of-stack$c-build-minor-frames
    (implies (and (stack$c-okp stack$c)
                  (< (nfix top) (stack$c-top-minor stack$c))
                  (<= (nfix bottom) (nfix top)))
             (equal (minor-stack-scratch-len frames)
                    (nfix (- (scratch-nontagidx-to-index
                              (stack$c-frame-next-scratchi (nfix top) stack$c))
                             (if (zp bottom)
                                 0
                               (scratch-nontagidx-to-index
                                (stack$c-frame-next-scratchi (1- (nfix bottom)) stack$c)))))))
    :hints(("Goal" :in-theory (enable minor-stack-scratch-len
                                      stack$c-next-scratch-ordered-necc-nfix))))

  (local (defun-nx nth-scratch-ind (n bottom top stack$c)
           (declare (xargs :measure (nfix top)))
           (b* ((frame (stack$c-build-minor-frame top (stack$c-frame-next-scratchi top stack$c) stack$c))
                (len (len (minor-frame->scratch frame)))
                ((when (< (nfix n) len))
                 stack$c))
             (and (< (lnfix bottom) (lnfix top))
                  (nth-scratch-ind (- (nfix n) len) bottom (1- (lnfix top)) stack$c)))))
           

  (defret nth-scratch-of-<fn>
    (implies (and (stack$c-okp stack$c)
                  (< (nfix top) (stack$c-top-minor stack$c))
                  (<= (nfix bottom) (nfix top))
                  (< (nfix n) (minor-stack-scratch-len frames)))
             (equal (minor-stack-nth-scratch n frames)
                    (stack$c-scratch-entry
                     (index-to-scratch-nontagidx
                      (- (scratch-nontagidx-to-index
                          (stack$c-frame-next-scratchi (nfix top) stack$c))
                         (+ 1 (nfix n))))
                     stack$c)))
    :hints(("Goal" :in-theory (enable minor-stack-scratch-len
                                      minor-stack-nth-scratch
                                      stack$c-next-scratch-ordered-necc-nfix)
            :induct (nth-scratch-ind n bottom top stack$c)
            :expand <call>))))




;; (local (in-theory (disable cons-equal)))

(local
 (defsection stack$c-build-minor-frames-of-update
   (local (defthm nfix-integer-compare
            (implies (and (integerp x) (integerp y)
                          (<= x y))
                     (<= (nfix x) (nfix y)))))

   (local (defthm nfix-dumb
            (implies (and (< (nfix x) y)
                          (integerp y))
                     (<= (nfix (+ -1 (nfix x))) (+ -1 y)))
            :hints(("Goal" :in-theory (enable nfix)))))

   (local (defthm nfix-dumb2
            (implies (and (< (nfix x) y)
                          (integerp y))
                     (<= (nfix (+ -1 (nfix x))) y))
            :hints(("Goal" :in-theory (enable nfix)))))

   (local (defthm nfix-dumb3
            (<= (nfix (+ -1 (nfix x))) (nfix x))
            :hints(("Goal" :in-theory (enable nfix)))))
   (def-updater-independence-thm stack$c-build-minor-frames-of-update
     (implies (and (range-nth-nontag-equiv-min-max (nfix (+ -1 (nfix bottom)))
                                                   top
                                                   (nth *stack$c-frame-next-scratchi1* new)
                                                   (nth *stack$c-frame-next-scratchi1* old))
                   (range-scratch-entry-equiv 1
                                              (stack$c-frame-next-scratchi top old)
                                              new old)
                   (stobjs::range-equal-min-max (* 3 (nfix bottom))
                                                (+ 2 (* 3 (nfix top)))
                                                (nth *stack$c-minori* new)
                                                (nth *stack$c-minori* old))
                   (<= (nfix bottom) (nfix top))
                   (stack$c-next-scratch-ordered (+ 1 (nfix top)) old)
                   (stack$c-next-scratch-bounded (+ 1 (nfix top)) old))
              (equal (stack$c-build-minor-frames bottom top new)
                     (stack$c-build-minor-frames bottom top old)))
     :hints(("Goal" :in-theory (e/d (stack$c-build-minor-frames
                                     stobjs::nth-when-range-equal-min-max
                                     nth-nontag-when-range-nth-nontag-equiv-min-max)
                                    (range-scratch-entry-equiv-by-badguy-literal)))
            (and stable-under-simplificationp
                 '(:cases ((zp bottom))))))))


(define stack$c-build-major-frame ((n natp) (stack$c stack$c-okp))
  :returns (frame major-frame-p)
  :guard (< n (stack$c-top-frame stack$c))
  :guard-debug t
  (make-major-frame :bindings (stack$c-majori (* 3 (lnfix n)) stack$c)
                    :rule (stack$c-majori (+ 1 (* 3 (lnfix n))) stack$c)
                    :phase (stack$c-majori (+ 2 (* 3 (lnfix n))) stack$c)
                    :minor-stack
                    (stack$c-build-minor-frames
                     (if (eql (lnfix n) 0)
                         0
                       (+ 1 (stack$c-frame-top-minori (1- n) stack$c)))
                     (stack$c-frame-top-minori n stack$c)
                     stack$c))
  ///
  (defret minor-stack-scratch-len-of-stack$c-build-major-frame
    (implies (and (stack$c-okp stack$c)
                  (< (nfix n) (stack$c-top-frame stack$c)))
             (equal (minor-stack-scratch-len (major-frame->minor-stack frame))
                    (nfix (- (scratch-nontagidx-to-index
                              (stack$c-frame-next-scratchi
                               (stack$c-frame-top-minori n stack$c)
                               stack$c))
                             (if (zp n)
                                 0
                               (scratch-nontagidx-to-index
                                (stack$c-frame-next-scratchi
                                 (stack$c-frame-top-minori (1- (nfix n)) stack$c)
                                 stack$c))))))))

  (defret nth-scratch-of-<fn>
    (implies (and (stack$c-okp stack$c)
                  (< (nfix n) (stack$c-top-frame stack$c))
                  (< (nfix k) (minor-stack-scratch-len (major-frame->minor-stack frame))))
             (equal (minor-stack-nth-scratch k (major-frame->minor-stack frame))
                    (stack$c-scratch-entry
                     (index-to-scratch-nontagidx
                      (- (scratch-nontagidx-to-index
                          (stack$c-frame-next-scratchi
                           (stack$c-frame-top-minori n stack$c)
                           stack$c))
                         (+ 1 (nfix k))))
                     stack$c)))))


(local
 (defsection stack$c-build-major-frame-of-update
   (def-updater-independence-thm stack$c-build-major-frame-of-update
     (b* ((bottom (if (zp n) 0 (+ 1 (stack$c-frame-top-minori (+ -1 (nfix n)) old))))
          (top (stack$c-frame-top-minori n old)))
       (implies (and (range-nth-nat-equiv-min-max (+ -1 (nfix n))
                                                  n
                                                  (nth *stack$c-frame-top-minori1* new)
                                                  (nth *stack$c-frame-top-minori1* old))
                     (stobjs::range-equal-min-max (* 3 (nfix n))
                                                  (+ 2 (* 3 (nfix n)))
                                                  (nth *stack$c-majori* new)
                                                  (nth *stack$c-majori* old))
                     (range-nth-nontag-equiv-min-max (nfix (+ -1 (nfix bottom)))
                                                     top
                                                     (nth *stack$c-frame-next-scratchi1* new)
                                                     (nth *stack$c-frame-next-scratchi1* old))
                     (range-scratch-entry-equiv 1
                                                (stack$c-frame-next-scratchi top old)
                                                new old)
                     (stobjs::range-equal-min-max (* 3 (nfix bottom))
                                                  (+ 2 (* 3 (nfix top)))
                                                  (nth *stack$c-minori* new)
                                                  (nth *stack$c-minori* old))
                     (<= (nfix bottom) (nfix top))
                     (stack$c-next-scratch-ordered (+ 1 (nfix top)) old)
                     (stack$c-next-scratch-bounded (+ 1 (nfix top)) old))
                (equal (stack$c-build-major-frame n new)
                       (stack$c-build-major-frame n old))))
     :hints(("Goal" :in-theory (e/d (stack$c-build-major-frame
                                     stobjs::nth-when-range-equal-min-max
                                     nth-nat-when-range-nth-nat-equiv-min-max)))))))


(define stack$c-build-top-major-frame ((stack$c stack$c-okp))
  :returns (frame major-frame-p)
  :guard-debug t
  (b* ((n (stack$c-top-frame stack$c))
       (top (stack$c-top-minor stack$c))
       (bottom (if (eql (lnfix n) 0)
                   0
                 (+ 1 (stack$c-frame-top-minori (1- n) stack$c)))))
    (make-major-frame :bindings (stack$c-majori (* 3 (lnfix n)) stack$c)
                      :rule (stack$c-majori (+ 1 (* 3 (lnfix n))) stack$c)
                      :phase (stack$c-majori (+ 2 (* 3 (lnfix n))) stack$c)
                      :minor-stack
                      (cons
                       (stack$c-build-minor-frame
                        top (stack$c-next-scratch stack$c) stack$c)
                       (and (< bottom top)
                            (stack$c-build-minor-frames bottom (+ -1 top) stack$c)))))
  ///
  (defret minor-stack-scratch-len-of-stack$c-build-top-major-frame
    (implies (stack$c-okp stack$c)
             (equal (minor-stack-scratch-len (major-frame->minor-stack frame))
                    (nfix (- (scratch-nontagidx-to-index
                              (stack$c-next-scratch stack$c))
                             (if (zp (stack$c-top-frame stack$c))
                                 0
                               (scratch-nontagidx-to-index
                                (stack$c-frame-next-scratchi
                                 (stack$c-frame-top-minori (1- (stack$c-top-frame stack$c)) stack$c)
                                 stack$c)))))))
    :hints(("Goal" :in-theory (enable minor-stack-scratch-len))))

  (defret nth-scratch-of-<fn>
    (implies (and (stack$c-okp stack$c)
                  (< (nfix k) (minor-stack-scratch-len (major-frame->minor-stack frame))))
             (equal (minor-stack-nth-scratch k (major-frame->minor-stack frame))
                    (stack$c-scratch-entry
                     (index-to-scratch-nontagidx
                      (- (scratch-nontagidx-to-index
                          (stack$c-next-scratch stack$c))
                         (+ 1 (nfix k))))
                     stack$c)))
    :hints(("Goal" :in-theory (enable minor-stack-nth-scratch
                                      minor-stack-scratch-len)))))


(local
 (defsection stack$c-build-top-major-frame-of-update
   (local (defthm nfix-integer-compare
            (implies (and (integerp x) (integerp y)
                          (<= x y))
                     (<= (nfix x) (nfix y)))))

   (def-updater-independence-thm stack$c-build-top-major-frame-of-update
     (b* ((n (stack$c-top-frame old))
          (bottom (if (zp n) 0 (+ 1 (stack$c-frame-top-minori (+ -1 (nfix n)) old))))
          (top (stack$c-top-minor old)))
       (implies (and (equal (stack$c-top-frame new)
                            (stack$c-top-frame old))
                     (equal (stack$c-top-minor new)
                            (stack$c-top-minor old))
                     (equal (stack$c-next-scratch new)
                            (stack$c-next-scratch old))
                     (range-nth-nat-equiv-min-max (+ -1 (nfix n))
                                                  n
                                                  (nth *stack$c-frame-top-minori1* new)
                                                  (nth *stack$c-frame-top-minori1* old))
                     (stobjs::range-equal-min-max (* 3 (nfix n))
                                                  (+ 2 (* 3 (nfix n)))
                                                  (nth *stack$c-majori* new)
                                                  (nth *stack$c-majori* old))
                     (range-nth-nontag-equiv-min-max (nfix (+ -1 (nfix bottom)))
                                                     top
                                                     (nth *stack$c-frame-next-scratchi1* new)
                                                     (nth *stack$c-frame-next-scratchi1* old))
                     (range-scratch-entry-equiv 1
                                                (stack$c-next-scratch old)
                                                new old)
                     (stobjs::range-equal-min-max (* 3 (nfix bottom))
                                                  (+ 2 (* 3 (nfix top)))
                                                  (nth *stack$c-minori* new)
                                                  (nth *stack$c-minori* old))
                     (<= (nfix bottom) (nfix top))
                     (stack$c-next-scratch-ordered (+ 1 (nfix top)) old)
                     (stack$c-next-scratch-bounded (+ 1 (nfix top)) old))
                (equal (stack$c-build-top-major-frame new)
                       (stack$c-build-top-major-frame old))))
     :hints(("Goal" :in-theory (e/d (stack$c-build-top-major-frame
                                     stobjs::nth-when-range-equal-min-max
                                     nth-nat-when-range-nth-nat-equiv-min-max
                                     nth-nontag-when-range-nth-nontag-equiv-min-max)))
            (and stable-under-simplificationp
                 '(:cases ((posp (stack$C-top-minor old)))))
            ))))


(define stack$c-build-major-frames ((top natp) (stack$c stack$c-okp))
  :returns (frames major-stack-p)
  :measure (lnfix top)
  :ruler-extenders (cons)
  :guard (< top (stack$c-top-frame stack$c))
  :guard-debug t
  :guard-hints (("goal" :do-not-induct t
                 ;; :cases ((< top (stack$c-top-frame stack$c)))
                 ))
  (cons (stack$c-build-major-frame top stack$c)
        (and (not (eql (lnfix top) 0))
             (stack$c-build-major-frames (1- (lnfix top)) stack$c)))
  ///
  (defthm len-of-stack$c-build-major-frames
    (equal (len (stack$c-build-major-frames top stack$c))
           (+ 1 (nfix top)))
    :hints(("Goal" :in-theory (enable len))))

  (local (defun nth-ind (n top)
           (if (zp top)
               n
             (nth-ind (+ -1 (nfix n)) (+ -1 top)))))

  (defthm nth-of-stack$c-build-major-frames
    (implies (<= (nfix n) (nfix top))
             (equal (nth n (stack$c-build-major-frames top stack$c))
                    (stack$c-build-major-frame (- (nfix top) (nfix n)) stack$c)))
    :hints(("Goal" :induct (nth-ind n top)
            :expand ((:free (a b) (nth n (cons a b)))
                     (stack$c-build-major-frames top stack$c)))))

  (defret major-stack-scratch-len-of-<fn>
    (implies (And (stack$c-okp stack$c)
                  (< (nfix top) (stack$c-top-frame stack$c)))
             (equal (major-stack-scratch-len frames)
                    (scratch-nontagidx-to-index
                     (stack$c-frame-next-scratchi
                      (stack$c-frame-top-minori top stack$c)
                      stack$c))))
    :hints(("Goal" :in-theory (enable major-stack-scratch-len))))

  (defret major-stack-scratch-len-of-<fn>
    (implies (And (stack$c-okp stack$c)
                  (< (nfix top) (stack$c-top-frame stack$c)))
             (equal (major-stack-scratch-len frames)
                    (scratch-nontagidx-to-index
                     (stack$c-frame-next-scratchi
                      (stack$c-frame-top-minori top stack$c)
                      stack$c))))
    :hints(("Goal" :in-theory (enable major-stack-scratch-len))))

  (local (defun-nx nth-scratch-ind (k top stack$c)
           (declare (xargs :measure (lnfix top)))
           (b* ((frame (stack$c-build-major-frame top stack$c))
                (len (minor-stack-scratch-len (major-frame->minor-stack frame)))
                ((when (< (nfix k) len)) stack$c))
             (and (not (eql (lnfix top) 0))
                  (nth-scratch-ind (- (nfix k) len) (1- (lnfix top)) stack$c)))))

  (defret nth-scratch-of-<fn>
    (implies (and (stack$c-okp stack$c)
                  (< (nfix top) (stack$c-top-frame stack$c))
                  (< (nfix k) (major-stack-scratch-len frames)))
             (equal (major-stack-nth-scratch k frames)
                    (stack$c-scratch-entry
                     (index-to-scratch-nontagidx
                      (- (scratch-nontagidx-to-index
                          (stack$c-frame-next-scratchi
                           (stack$c-frame-top-minori top stack$c)
                           stack$c))
                         (+ 1 (nfix k))))
                     stack$c)))
    :hints (("goal" :induct (nth-scratch-ind k top stack$c)
             :in-theory (enable major-stack-nth-scratch
                                major-stack-scratch-len)
             :expand <call>))))


(local
 (defsection stack$c-build-major-frames-of-update
   (local (defthm nfix-integer-compare
            (implies (and (integerp x) (integerp y)
                          (<= x y))
                     (<= (nfix x) (nfix y)))))

   (def-updater-independence-thm stack$c-build-major-frames-of-update
     (b* ((top (stack$c-frame-top-minori n old)))
       (implies (and (range-nth-nat-equiv-min-max 0
                                                  n
                                                  (nth *stack$c-frame-top-minori1* new)
                                                  (nth *stack$c-frame-top-minori1* old))
                     (stobjs::range-equal-min-max 0
                                                  (+ 2 (* 3 (nfix n)))
                                                  (nth *stack$c-majori* new)
                                                  (nth *stack$c-majori* old))
                     (range-nth-nontag-equiv-min-max 0
                                                     top
                                                     (nth *stack$c-frame-next-scratchi1* new)
                                                     (nth *stack$c-frame-next-scratchi1* old))
                     (range-scratch-entry-equiv 1
                                                (stack$c-frame-next-scratchi top old)
                                                new old)
                     (stobjs::range-equal-min-max 0
                                                  (+ 2 (* 3 (nfix top)))
                                                  (nth *stack$c-minori* new)
                                                  (nth *stack$c-minori* old))
                     (stack$c-next-scratch-ordered (+ 1 (nfix top)) old)
                     (stack$c-next-scratch-bounded (+ 1 (nfix top)) old)
                     (stack$c-top-minor-ordered (+ 1 (nfix n)) old)
                     (stack$c-top-minor-bounded (+ 1 (nfix n)) old))
                (equal (stack$c-build-major-frames n new)
                       (stack$c-build-major-frames n old))))
     :hints(("Goal" :in-theory (e/d (stack$c-build-major-frames)
                                    (range-scratch-entry-equiv-by-badguy-literal)))))))

(define stack$c-extract ((stack$c stack$c-okp))
  :returns (stack major-stack-p)
  (cons (stack$c-build-top-major-frame stack$c)
        (and (< 0 (stack$c-top-frame stack$c))
             (stack$c-build-major-frames (+ -1 (stack$c-top-frame stack$c)) stack$c)))
  ///
  (defthm len-of-stack$c-extract
    (equal (len (stack$c-extract stack$c))
           (+ 1 (stack$c-top-frame stack$c)))
    :hints(("Goal" :in-theory (enable len))))

  

  (defret major-stack-scratch-len-of-<fn>
    (implies (stack$c-okp stack$c)
             (equal (major-stack-scratch-len stack)
                    (scratch-nontagidx-to-index (stack$c-next-scratch stack$c))))
    :hints(("Goal" :in-theory (enable major-stack-scratch-len))))

  (defret major-stack-nth-scratch-of-<fn>
    (implies (and (stack$c-okp stack$c)
                  (< (nfix k) (major-stack-scratch-len stack)))
             (equal (major-stack-nth-scratch k stack)
                    (stack$c-scratch-entry
                     (index-to-scratch-nontagidx
                      (- (scratch-nontagidx-to-index (stack$c-next-scratch stack$c))
                         (+ 1 (nfix k))))
                     stack$c)))
    :hints(("Goal" :in-theory (enable major-stack-nth-scratch
                                      major-stack-scratch-len)))))






















;;   (and (<= (+ 2 (* 3 (stack$c-top-frame stack$c))) (stack$c-major-length stack$c))
;;        (<= (+ 2 (* 3 (stack$c-top-minor stack$c))) (stack$c-minor-length stack$c))
;;        (< (stack$c-top-frame stack$c) (stack$c-frame-top-minor-length stack$c))
;;        (< (stack$c-top-minor stack$c) (stack$c-frame-next-scratch-length stack$c))
;;        (<= (stack$c-next-scratch stack$c) (stack$c-scratch-length stack$c))))

(define update-scratch-codeslot ((tail natp :type (unsigned-byte 32))
                                 (val :type (unsigned-byte 60))
                                 (stack$c stack$c-bounds-ok))
  :guard (and (< (ash tail 4) (stack$c-next-scratch stack$c))
              (ec-call (stack$c-scratch-codeslots-ok stack$c)))
  :returns new-stack$c
  (update-stack$c-scratchi (ash (nfix tail) 4)
                           (loghead 60 val)
                           stack$c)
  ///
  (defret stack$c-scratch-codeslots-ok-of-<fn>
    (implies (and (stack$c-scratch-codeslots-ok stack$c)
                  ;; (< (ash (nfix tail) 4) (stack$c-next-scratch stack$c))
                  )
             (stack$c-scratch-codeslots-ok new-stack$c))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable max)))))

  (defret stack$c-bounds-ok-of-<fn>
    (implies (and (stack$c-bounds-ok stack$c)
                  ;; (< (ash (nfix tail) 4) (stack$c-next-scratch stack$c))
                  )
             (stack$c-bounds-ok new-stack$c))
    :hints (("goal" :in-theory (enable max len-of-update-nth-scratch))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (local (defthm equal-ash
           (implies (natp n)
                    (equal (equal (ash x n) (ash y n)) 
                           (equal (ifix x) (ifix y))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (defthm scratch-codeslot-of-update-scratch-codeslot
    (equal (scratch-codeslot m (update-scratch-codeslot n val stack$c))
           (if (equal (nfix n) (nfix m))
               (loghead 60 val)
             (scratch-codeslot m stack$c)))
    :hints(("Goal" :in-theory (enable scratch-codeslot))))

  (defthm stack$c-scratchi-of-update-scratch-codeslot
    (implies (not (equal 0 (loghead 4 (nfix m))))
             (equal (nth-scratch m (nth *stack$c-scratchi1* (update-scratch-codeslot tail val stack$c)))
                    (nth-scratch m (nth *stack$c-scratchi1* stack$c)))))

  (defret len-scratch-of-<fn>
    ;; (implies (and (stack$c-bounds-ok stack$c)
    ;;               (< (ash (nfix tail) 4) (stack$c-next-scratch stack$c)))
    (>= (len (nth *stack$c-scratchi1* new-stack$c))
        (len (nth *stack$c-scratchi1* stack$c)))
    :hints(("Goal" :in-theory (enable len-of-update-nth-scratch)))
    :rule-classes :linear)

  (defret nth-of-<fn>
    (implies (not (equal (nfix n) *stack$c-scratchi1*))
             (equal (nth n new-stack$c) (nth n stack$c)))))


(define update-scratch-entry-codeslot ((n natp :type (unsigned-byte 32))
                                       (val :type (unsigned-byte 60))
                                       (stack$c stack$c-bounds-ok))
  :guard (and (<= n (stack$c-next-scratch stack$c))
              (ec-call (stack$c-scratch-codeslots-ok stack$c)))
  :returns new-stack$c
  :inline t
  :enabled t
  :guard-hints (("goal" :in-theory (enable update-scratch-codeslot))
                (and stable-under-simplificationp
                     '(:in-theory (e/d (bitops::logsquash)
                                       (bitops::logand-with-negated-bitmask)))))
  (mbe :logic (update-scratch-codeslot (logtail 4 (nfix n)) val stack$c)
       :exec (update-stack$c-scratchi (the (unsigned-byte 32) (logand #x-10 (the (unsigned-byte 32) n)))
                                      (the (unsigned-byte 60) val)
                                      stack$c)))

(define update-scratch-codeslot-code ((n :type (unsigned-byte 4))
                                      (val :type (unsigned-byte 4))
                                      (codeslot :type (unsigned-byte 60)))
  :guard (not (eql 0 n))
  :returns (new-codeslot natp :rule-classes :type-prescription)
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable ash-2-is-*-4)
                       :do-not-induct t
                       :expand ((:with unsigned-byte-p (unsigned-byte-p 4 n))))))
  :prepwork ((local (defthmd ash-2-is-*-4
                      (equal (ash x 2)
                             (* 4 (ifix x)))
                      :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x)))))
             (local (defthm loghead-4-upper-bound
                      (<= (loghead 4 x) 15)
                      :hints (("goal" :use ((:instance acl2::unsigned-byte-p-of-loghead
                                             (size1 4) (size 4) (i x)))
                               :in-theory (e/d (unsigned-byte-p)
                                               (acl2::unsigned-byte-p-of-loghead))))
                      :rule-classes :linear))
             (local (defthm pos-fix-loghead-4-upper-bound
                      (<= (pos-fix (loghead 4 x)) 15)
                      :hints(("Goal" :in-theory (enable pos-fix)))
                      :rule-classes :linear))
             (local (defthm unsigned-byte-p-4-of-15
                      (implies (and (integerp n)
                                    (<= 4 n))
                               (unsigned-byte-p n 15))))
             (local (defthm signed-byte-p-5-of-15
                      (implies (and (integerp n)
                                    (<= 5 n))
                               (signed-byte-p n 15)))))
  (b* ((shift (the (unsigned-byte 6)
                   (ash (the (unsigned-byte 4)
                             (+ -1 
                                (the (unsigned-byte 4)
                                     (mbe :logic (lposfix (loghead 4 n))
                                          :exec n))))
                        2)))
       (mask (the (signed-byte 61)
                  (lognot
                   (the (unsigned-byte 60)
                        (ash #xf
                             (the (unsigned-byte 6) shift)))))))
    (the (unsigned-byte 60)
         (logior (the (unsigned-byte 60)
                      (logand (the (unsigned-byte 60)
                                   (mbe :logic (loghead 60 codeslot)
                                        :exec codeslot))
                              (the (signed-byte 61) mask)))
                 (the (unsigned-byte 60)
                      (ash (the (unsigned-byte 4)
                                (mbe :logic (loghead 4 val)
                                     :exec val))
                           shift)))))
  ///
  (defret unsigned-byte-60-of-<fn>
    (unsigned-byte-p 60 new-codeslot)
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable ash-2-is-*-4)
                   :do-not-induct t))))

  (local (in-theory (disable acl2::loghead-identity
                             scratch-nontagidx-implies-linear
                             scratch-nontagidx-p-when-loghead
                             acl2::natp-posp
                             acl2::posp-redefinition
                             acl2::posp-rw
                             acl2::<-0-+-negative-1
                             acl2::zp-when-gt-0
                             acl2::ash-0
                             bitops::logior-<-0-linear-2)))

  (defret scratch-codeslot-code-of-update-scratch-codeslot-code
    (equal (scratch-codeslot-code m (update-scratch-codeslot-code n val codeslot))
           (if (equal (pos-fix (loghead 4 m))
                      (pos-fix (loghead 4 n)))
               (loghead 4 val)
             (scratch-codeslot-code m codeslot)))
    :hints(("Goal" :in-theory (enable scratch-codeslot-code))
           (and stable-under-simplificationp
                '(:in-theory (enable ash-2-is-*-4)
                  :do-not-induct t))
           (bitops::equal-by-logbitp-hammer))))


(define update-scratch-entry-kindcode ((n natp :type (unsigned-byte 32))
                                       (code :type (unsigned-byte 4))
                                       (stack$c stack$c-bounds-ok))
  :guard (and (<= n (stack$c-next-scratch stack$c))
              (not (eql 0 (loghead 4 n)))
              (ec-call (stack$c-scratch-codeslots-ok stack$c)))
  :inline t
  :returns new-stack$c
  (b* ((codeslot (scratch-entry-codeslot n stack$c))
       (new-codeslot (update-scratch-codeslot-code
                      (the (unsigned-byte 4) (logand #xf (lnfix n)))
                      code codeslot)))
    (update-scratch-entry-codeslot n new-codeslot stack$c))
  ///
  
  (defret stack$c-scratch-codeslots-ok-of-<fn>
    (implies (and (stack$c-scratch-codeslots-ok stack$c)
                  ;; (< (nfix n) (stack$c-next-scratch stack$c))
                  )
             (stack$c-scratch-codeslots-ok new-stack$c))
    :hints(("Goal" :in-theory (e/d (bitops::logsquash)
                                   (bitops::logand-with-negated-bitmask)))))
  

  (defret stack$c-bounds-ok-of-<fn>
    (implies (and (stack$c-bounds-ok stack$c)
                  ;; (< (nfix n) (stack$c-next-scratch stack$c))
                  )
             (stack$c-bounds-ok new-stack$c)))

  (defret len-scratch-of-<fn>
    ;; (implies (and (stack$c-bounds-ok stack$c)
    ;;               (< (ash (nfix tail) 4) (stack$c-next-scratch stack$c)))
    (>= (len (nth *stack$c-scratchi1* new-stack$c))
        (len (nth *stack$c-scratchi1* stack$c)))
    :rule-classes :linear)

  (local (Defthm equal-of-loghead-when-logtail-equal
           (implies (equal (logtail n x) (logtail n y))
                    (equal (equal (loghead n x) (loghead n y))
                           (equal (ifix x) (ifix y))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (defthm scratch-entry-kindcode-of-update-scratch-entry-kindcode
    (implies (and (not (equal 0 (loghead 4 (nfix n))))
                  (not (equal 0 (loghead 4 (nfix m)))))
             (equal (scratch-entry-kindcode m (update-scratch-entry-kindcode n val stack$c))
                    (if (equal (nfix n) (nfix m))
                        (loghead 4 val)
                      (scratch-entry-kindcode m stack$c))))
    :hints(("Goal" :in-theory (enable scratch-entry-kindcode))))

  (defthm stack$c-scratchi-of-update-scratch-entry-kindcode
    (implies (not (equal 0 (loghead 4 (nfix m))))
             (equal (nth-scratch m (nth *stack$c-scratchi1* (update-scratch-entry-kindcode tail val stack$c)))
                    (nth-scratch m (nth *stack$c-scratchi1* stack$c)))))

  (defret nth-of-<fn>
    (implies (not (equal (nfix m) *stack$c-scratchi1*))
             (equal (nth m new-stack$c) (nth m stack$c))))

  (defret len-scratch-of-<fn>
    (<= (len (nth *stack$c-scratchi1* stack$c))
        (len (nth *stack$c-scratchi1* new-stack$c)))
    :rule-classes :linear))





(local (defthmd update-nth-redundant-free
         (implies (and (equal val (nth n x))
                       (< (nfix n) (len x)))
                  (equal (update-nth n val x) x))
         :hints(("Goal" :in-theory (enable nth update-nth len)))))

(define update-stack$c-scratch-entry ((n scratch-nontagidx-p)
                                      (obj scratchobj-p)
                                      (stack$c stack$c-okp))
  :guard (<= n (stack$c-next-scratch stack$c))
  :returns (new-stack$c)
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable len-of-update-nth-scratch)))
  (b* ((n (scratch-nontagidx-fix n))
       (code (scratchobj-kind->code (scratchobj-kind obj)))
       (val (scratchobj->val obj))
       (stack$c (update-stack$c-scratchi n val stack$c)))
    (update-scratch-entry-kindcode n code stack$c))
  ///
  (defthm stack$c-scratch-entry-of-update-stack$c-scratch-entry
    (equal (stack$c-scratch-entry m (update-stack$c-scratch-entry n obj stack$c))
           (if (scratch-nontagidx-equiv n m)
               (scratchobj-fix obj)
             (stack$c-scratch-entry m stack$c)))
    :hints(("Goal" :in-theory (enable stack$c-scratch-entry))))

  (defthm nth-of-update-stack$c-scratch-entry
    (implies (not (equal (nfix m) *stack$c-scratchi1*))
             (equal (nth m (update-stack$c-scratch-entry n obj stack$c))
                    (nth m stack$c))))


  (local (in-theory (enable len-of-update-nth-scratch)))

  (defret stack$c-okp-of-<fn>
    (implies (stack$c-okp stack$c)
             (stack$c-okp new-stack$c))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (member (car lit) '(stack$c-major-frames-welltyped
                                            stack$c-minor-frames-welltyped
                                            stack$c-major-frames-bounded
                                            stack$c-minor-frames-bounded
                                            stack$c-top-minor-ordered
                                            stack$c-scratch-codeslots-ok
                                            stack$c-next-scratch-ordered
                                            stack$c-next-scratch-bounded
                                            stack$c-top-minor-bounded
                                            stack$c-scratch-welltyped))
                        `(:expand (,lit)))))))

  (defret scratchobj-code/val-okp-of-<fn>
    (b* ((code (scratch-entry-kindcode n new-stack$c))
         (val (nth-scratch n (nth *stack$c-scratchi1* new-stack$c))))
      (implies (scratch-nontagidx-p n)
               (scratchobj-code/val-okp code val))))

  (defret len-scratch-of-<fn>
    (<= (len (nth *stack$c-scratchi1* stack$c))
        (len (nth *stack$c-scratchi1* new-stack$c)))
    :rule-classes :linear))

(local
 (defsection range-scratch-entry-equiv-of-update-stack$c-scratch-entry-out-of-range
   (local (in-theory (enable update-stack$c-scratch-entry)))

   (defthm range-scratch-entry-equiv-of-update-stack$c-scratch-entry-out-of-range-2
     (implies (and (scratch-nontagidx-p i)
                   (not (and (<= (scratch-nontagidx-fix min) i)
                             (< i (scratch-nontagidx-fix max)))))
              (iff (range-scratch-entry-equiv min max x (update-stack$c-scratch-entry i obj y))
                   (range-scratch-entry-equiv min max x y)))
     :hints (("goal" :in-theory (enable range-scratch-entry-equiv-necc))))

   (defthm range-scratch-entry-equiv-of-update-stack$c-scratch-entry-out-of-range-1
     (implies (and (scratch-nontagidx-p i)
                   (not (and (<= (scratch-nontagidx-fix min) i)
                             (< i (scratch-nontagidx-fix max)))))
              (iff (range-scratch-entry-equiv min max (update-stack$c-scratch-entry i obj x) y)
                   (range-scratch-entry-equiv min max x y)))
     :hints (("goal" :use ((:instance range-scratch-entry-equiv-of-update-stack$c-scratch-entry-out-of-range-2
                            (x y) (y x)))
              :in-theory (e/d (range-scratch-entry-equiv-commute)
                              (range-scratch-entry-equiv-of-update-stack$c-scratch-entry-out-of-range-2)))))))




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
    :hints(("Goal" :in-theory (enable nth-nat))))
  
  (defthm nth-scratch-of-maybe-grow-list
    (let ((new-list (maybe-grow-list threshold 0 list)))
       (equal (nth-scratch n new-list) (nth-scratch n list)))
     :hints(("Goal" :in-theory (enable nth-scratch))))

  (defthm nth-nontag-of-maybe-grow-list
    (equal (nth-nontag n (maybe-grow-list threshold 1 list))
           (nth-nontag n list))
    :hints(("Goal" :in-theory (enable nth-nontag))))

  (local (in-theory (disable maybe-grow-list)))

  (defthm stack$c-scratch-codeslots-ok-of-maybe-grow
    (implies (stack$c-scratch-codeslots-ok stack$c)
             (stack$c-scratch-codeslots-ok
              (update-nth *stack$c-scratchi1*
                          (maybe-grow-list n 0 (nth *stack$c-scratchi1* stack$c))
                          stack$c)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable max)))))

  (defthm stack$c-scratch-welltyped-of-maybe-grow
    (implies (stack$c-scratch-welltyped stack$c)
             (stack$c-scratch-welltyped
              (update-nth *stack$c-scratchi1*
                          (maybe-grow-list n 0 (nth *stack$c-scratchi1* stack$c))
                          stack$c)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))



(define maybe-resize-stack$c-major ((n natp) stack$c)
  :enabled t
  :guard-hints (("goal" :in-theory (enable maybe-grow-list
                                           update-nth-redundant-free)))
  (mbe :logic (non-exec (update-nth *stack$c-majori*
                                    (maybe-grow-list
                                     n nil
                                     (nth *stack$c-majori* stack$c))
                                    stack$c))
       :exec (if (< (stack$c-major-length stack$c) n)
                 (resize-stack$c-major (max 16 (* 2 n)) stack$c)
               stack$c)))

(define maybe-resize-stack$c-minor ((n natp) stack$c)
  :enabled t
  :guard-hints (("goal" :in-theory (enable maybe-grow-list
                                           update-nth-redundant-free)))
  (mbe :logic (non-exec (update-nth *stack$c-minori*
                                    (maybe-grow-list
                                     n nil
                                     (nth *stack$c-minori* stack$c))
                                    stack$c))
       :exec (if (< (stack$c-minor-length stack$c) n)
                 (resize-stack$c-minor (max 16 (* 2 n)) stack$c)
               stack$c)))

(define maybe-resize-stack$c-frame-top-minor ((n natp) stack$c)
  :enabled t
  :guard-hints (("goal" :in-theory (enable maybe-grow-list
                                           update-nth-redundant-free)))
  (mbe :logic (non-exec (update-nth *stack$c-frame-top-minori1*
                                    (maybe-grow-list
                                     n 0
                                     (nth *stack$c-frame-top-minori1* stack$c))
                                    stack$c))
       :exec (if (< (stack$c-frame-top-minor-length stack$c) n)
                 (resize-stack$c-frame-top-minor (max 16 (* 2 n)) stack$c)
               stack$c)))

(define maybe-resize-stack$c-frame-next-scratch ((n natp) stack$c)
  :enabled t
  :guard-hints (("goal" :in-theory (enable maybe-grow-list
                                           update-nth-redundant-free)))
  (mbe :logic (non-exec (update-nth *stack$c-frame-next-scratchi1*
                                    (maybe-grow-list
                                     n 1
                                     (nth *stack$c-frame-next-scratchi1* stack$c))
                                    stack$c))
       :exec (if (< (stack$c-frame-next-scratch-length stack$c) n)
                 (resize-stack$c-frame-next-scratch (max 16 (* 2 n)) stack$c)
               stack$c)))

(define maybe-resize-stack$c-scratch ((n natp) stack$c)
  :enabled t
  :guard-hints (("goal" :in-theory (enable maybe-grow-list
                                           update-nth-redundant-free)))
  (mbe :logic (non-exec (update-nth *stack$c-scratchi1*
                                    (maybe-grow-list
                                     n 0
                                     (nth *stack$c-scratchi1* stack$c))
                                    stack$c))
       :exec (if (< (stack$c-scratch-length stack$c) n)
                 (resize-stack$c-scratch (max 16 (* 2 n)) stack$c)
               stack$c)))




(local (defthm less-than-increment-index-to-scratch-nontagidx
         (implies (and (scratch-nontagidx-p x)
                       (natp idx)
                       (<= (index-to-scratch-nontagidx idx) x))
                  (equal (< x (index-to-scratch-nontagidx (+ 1 idx)))
                         (equal x (index-to-scratch-nontagidx idx))))
         :hints (("goal" :cases ((< x (index-to-scratch-nontagidx (+ 1 idx)))))
                 (and stable-under-simplificationp
                      '(:use ((:instance scratch-nontagidx-to-index-monotonic
                               (x x) (y (index-to-scratch-nontagidx (+ 1 idx))))
                              (:instance scratch-nontagidx-to-index-monotonic
                               (y x) (x (index-to-scratch-nontagidx idx))))
                        :in-theory (disable scratch-nontagidx-to-index-monotonic))))))


;; (local
;;  (defthm scratch-decr-nontagidx-less-by-

(local
 (def-updater-independence-thm stack$c-next-scratch-ordered-of-update
   (implies (range-nth-nontag-equiv-min-max 0 (+ -1 (nfix limit))
                                            (nth *stack$c-frame-next-scratchi1* new)
                                            (nth *stack$c-frame-next-scratchi1* old))
            (iff (stack$c-next-scratch-ordered limit new)
                 (stack$c-next-scratch-ordered limit old)))
   :hints ((acl2::use-termhint
            (b* (((mv ?ord unord)
                  (if (stack$c-next-scratch-ordered limit old)
                      (mv old new)
                    (mv new old)))
                 ((mv i j) (stack$c-next-scratch-ordered-witness limit unord)))
              `(:expand ((stack$c-next-scratch-ordered limit ,(acl2::hq unord)))
                :use ((:instance stack$c-next-scratch-ordered-necc
                       (i ,(acl2::hq i))
                       (j ,(acl2::hq j))
                       (stack$c ,(acl2::hq ord))))
                :in-theory (e/d (nth-nontag-when-range-nth-nontag-equiv-min-max)
                                (stack$c-next-scratch-ordered-necc
                                 stack$c-next-scratch-ordered-when-greater))))))))

(local
 (def-updater-independence-thm stack$c-next-scratch-bounded-of-update
   (implies (and (range-nth-nontag-equiv-min-max 0 (+ -1 (nfix limit))
                                                 (nth *stack$c-frame-next-scratchi1* new)
                                                 (nth *stack$c-frame-next-scratchi1* old))
                 (equal (stack$c-next-scratch new)
                        (stack$c-next-scratch old)))
            (iff (stack$c-next-scratch-bounded limit new)
                 (stack$c-next-scratch-bounded limit old)))
   :hints ((acl2::use-termhint
            (b* (((mv ?ord unord)
                  (if (stack$c-next-scratch-bounded limit old)
                      (mv old new)
                    (mv new old)))
                 (j (stack$c-next-scratch-bounded-witness limit unord)))
              `(:expand ((stack$c-next-scratch-bounded limit ,(acl2::hq unord)))
                :use ((:instance stack$c-next-scratch-bounded-necc
                       (j ,(acl2::hq j))
                       (stack$c ,(acl2::hq ord))))
                :in-theory (e/d (nth-nontag-when-range-nth-nontag-equiv-min-max)
                                (stack$c-next-scratch-bounded-necc
                                 stack$c-next-scratch-bounded-when-greater))))))))



(local
 (def-updater-independence-thm stack$c-top-minor-ordered-of-update
   (implies (range-nth-nat-equiv-min-max 0 (+ -1 (nfix limit))
                                         (nth *stack$c-frame-top-minori1* new)
                                         (nth *stack$c-frame-top-minori1* old))
            (iff (stack$c-top-minor-ordered limit new)
                 (stack$c-top-minor-ordered limit old)))
   :hints ((acl2::use-termhint
            (b* (((mv ?ord unord)
                  (if (stack$c-top-minor-ordered limit old)
                      (mv old new)
                    (mv new old)))
                 ((mv i j) (stack$c-top-minor-ordered-witness limit unord)))
              `(:expand ((stack$c-top-minor-ordered limit ,(acl2::hq unord)))
                :use ((:instance stack$c-top-minor-ordered-necc
                       (i ,(acl2::hq i))
                       (j ,(acl2::hq j))
                       (stack$c ,(acl2::hq ord))))
                :in-theory (e/d (nth-nat-when-range-nth-nat-equiv-min-max)
                                (stack$c-top-minor-ordered-necc
                                 stack$c-top-minor-ordered-when-greater))))))))

(local
 (def-updater-independence-thm stack$c-top-minor-bounded-of-update
   (implies (and (range-nth-nat-equiv-min-max 0 (+ -1 (nfix limit))
                                                 (nth *stack$c-frame-top-minori1* new)
                                                 (nth *stack$c-frame-top-minori1* old))
                 (equal (stack$c-top-minor new)
                        (stack$c-top-minor old)))
            (iff (stack$c-top-minor-bounded limit new)
                 (stack$c-top-minor-bounded limit old)))
   :hints ((acl2::use-termhint
            (b* (((mv ?ord unord)
                  (if (stack$c-top-minor-bounded limit old)
                      (mv old new)
                    (mv new old)))
                 (j (stack$c-top-minor-bounded-witness limit unord)))
              `(:expand ((stack$c-top-minor-bounded limit ,(acl2::hq unord)))
                :use ((:instance stack$c-top-minor-bounded-necc
                       (j ,(acl2::hq j))
                       (stack$c ,(acl2::hq ord))))
                :in-theory (e/d (nth-nat-when-range-nth-nat-equiv-min-max)
                                (stack$c-top-minor-bounded-necc
                                 stack$c-top-minor-bounded-when-greater))))))))

(local
 (def-updater-independence-thm stack$c-top-minor-bounded-when-increased
   (implies (and (range-nth-nat-equiv-min-max 0 (+ -1 (nfix limit))
                                                 (nth *stack$c-frame-top-minori1* new)
                                                 (nth *stack$c-frame-top-minori1* old))
                 (> (stack$c-top-minor new) (stack$c-top-minor old))
                 (stack$c-top-minor-bounded limit old))
            (stack$c-top-minor-bounded limit new))
   :hints ((acl2::use-termhint
            (b* (((mv ?ord unord) 
                  (mv old new))
                 (j (stack$c-top-minor-bounded-witness limit unord)))
              `(:expand ((stack$c-top-minor-bounded limit ,(acl2::hq unord)))
                :use ((:instance stack$c-top-minor-bounded-necc
                       (j ,(acl2::hq j))
                       (stack$c ,(acl2::hq ord))))
                :in-theory (e/d (nth-nat-when-range-nth-nat-equiv-min-max)
                                (stack$c-top-minor-bounded-necc
                                 stack$c-top-minor-bounded-when-greater))))))))










;; (define scratch-nontag-diff-rec ((y scratch-nontagidx-p)
;;                                  (x scratch-nontagidx-p))
;;   :returns (diff natp :rule-classes :type-prescription)
;;   :measure (nfix (- (scratch-nontagidx-fix y) (scratch-nontagidx-fix x)))
;;   :hints (("goal" :in-theory (disable scratch-increment-index-in-terms-of-conversions)))
;;   :prepwork ((local (defthm <-neg
;;                       (equal (< (- x) (- y))
;;                              (< y x)))))
;;   (b* ((x (scratch-nontagidx-fix x))
;;        (y (scratch-nontagidx-fix y))
;;        ((when (<= y x)) 0))
;;     (+ 1 (scratch-nontag-diff-rec y (scratch-incr-nontagidx x))))
;;   ///
;;   (defthm scratch-nontag-diff-rec-in-terms-of-converts
;;     (equal (scratch-nontag-diff-rec y x)
;;            (nfix (- (scratch-nontagidx-to-index y)
;;                     (scratch-nontagidx-to-index x))))))


(define stack$c-frames ((stack$c stack$c-okp))
  (lposfix (+ 1 (stack$c-top-frame stack$c)))
  ///
  (defthm stack$a-frames-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$a-frames (stack$c-extract stack$c))
                    (stack$c-frames stack$c)))
    :hints(("Goal" :in-theory (enable stack$a-frames
                                      stack$c-extract
                                      len max)))))


(local (in-theory (disable natp acl2::natp-when-gte-0)))

(local (defthm unequal-by-mod-3-*-+
         (implies (not (equal (mod (* a b) 3)
                              (mod (+ c d) 3)))
                  (not (equal (* a b) (+ c d))))))

(local (defthm unequal-by-mod-3-+-+
         (implies (not (equal (mod (+ a b) 3)
                              (mod (+ c d) 3)))
                  (not (equal (+ a b) (+ c d))))))



(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
;; (local (defthm mod-3-of-plus
;;          (implies (natp n)
;;                   (equal (mod (* 3 n) 3) 0))))


(define stack$c-push-frame ((stack$c stack$c-okp))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable maybe-grow-list
                                          update-nth-redundant-free))))
  :returns new-stack$c
  :prepwork ((local (in-theory (disable cons-equal
                                        acl2::nth-when-atom
                                        true-listp-update-nth
                                        acl2::nth-when-too-large-cheap))))
  (b* ((prev-top-major (stack$c-top-frame stack$c))
       (stack$c (maybe-resize-stack$c-major (+ 6 (* 3 prev-top-major)) stack$c))
       (stack$c (maybe-resize-stack$c-frame-top-minor (+ 2 prev-top-major) stack$c))
       (prev-top-minor (stack$c-top-minor stack$c))
       (stack$c (maybe-resize-stack$c-minor (+ 6 (* 3 prev-top-minor)) stack$c))
       (stack$c (maybe-resize-stack$c-frame-next-scratch (+ 2 prev-top-minor) stack$c))
       (new-top-minor (+ 1 prev-top-minor))
       (stack$c (update-stack$c-frame-top-minori prev-top-major prev-top-minor stack$c))
       (stack$c (update-stack$c-top-minor new-top-minor stack$c))
       (next-scratch (stack$c-next-scratch stack$c))
       (stack$c (update-stack$c-frame-next-scratchi prev-top-minor next-scratch stack$c))
       (new-top-major (+ 1 prev-top-major))
       ;; (stack$c (update-stack$c-majori (+ 1 (* 3 new-top-major))
       ;;                                 '(:primitive fake-rule-for-new-stack-frame)
       ;;                                 stack$c))
       ;; (stack$c (update-stack$c-majori (+ 2 (* 3 new-top-major)) 0 stack$c))
       ;; (stack$c (update-stack$c-minori (+ 2 (* 3 new-top-minor)) 0 stack$c))
       )
    (update-stack$c-top-frame new-top-major stack$c))
  ///
  (local (defthm hack
           (implies (and (integerp a) (integerp b)
                         (< a (+ 1 b))
                         (not (equal a b)))
                    (< a b))))

  (local (defthm hack2
           (implies (and (integerp a) (integerp b)
                         (<= a (+ 1 b))
                         (case-split (not (equal a (+ 1 b)))))
                    (<= a b))))

  (defret stack$c-okp-of-<fn>
    (implies (stack$c-okp stack$c)
             (stack$c-okp new-stack$c))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (member (car lit) '(stack$c-major-frames-welltyped
                                            stack$c-minor-frames-welltyped
                                            stack$c-major-frames-bounded
                                            stack$c-minor-frames-bounded
                                            stack$c-top-minor-ordered
                                            stack$c-scratch-codeslots-ok
                                            stack$c-next-scratch-ordered
                                            stack$c-next-scratch-bounded
                                            stack$c-top-minor-bounded
                                            stack$c-scratch-welltyped))
                        `(:expand (,lit)))))))

  

  (defthm stack$a-push-frame-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$c-extract (stack$c-push-frame stack$c))
                    (stack$a-push-frame (stack$c-extract stack$c))))
    :hints(("Goal" :in-theory (enable stack$a-push-frame
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      stack$c-build-major-frame
                                      ;; stack$c-build-minor-frames
                                      )
            :expand ((:free (x)
                      (stack$c-build-major-frames
                       (nth-nat *stack$c-top-frame1* stack$c) x))
                     (:free (x)
                      (stack$c-build-major-frame
                       (nth-nat *stack$c-top-frame1* stack$c) x))
                     (:free (next x)
                      (stack$c-build-minor-frame
                       (+ 1 (nth-nat *stack$c-top-minor1* stack$c)) next x))
                     (:free (bottom x)
                      (stack$c-build-minor-frames
                       bottom (nth-nat *stack$c-top-minor1* stack$c) x))
                     )))))

(define stack$c-minor-frames ((stack$c stack$c-okp))
  (b* ((top-major (stack$c-top-frame stack$c))
       (top-minor (stack$c-top-minor stack$c))
       (prev-top-minor (if (eql 0 top-major)
                           -1
                         (stack$c-frame-top-minori (+ -1 top-major) stack$c))))
    (- top-minor prev-top-minor))
  ///
  (defthm stack$a-minor-frames-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$a-minor-frames (stack$c-extract stack$c))
                    (stack$c-minor-frames stack$c)))
    :hints(("Goal" :in-theory (enable stack$a-minor-frames
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      stack$c-build-minor-frame
                                      len max)))))



(define stack$c-push-minor-frame ((stack$c stack$c-okp))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable maybe-grow-list
                                          update-nth-redundant-free))))
  :returns new-stack$c
  (b* ((top-minor (stack$c-top-minor stack$c))
       (new-top-minor (+ 1 top-minor))
       (stack$c (maybe-resize-stack$c-minor (+ 3 (* 3 new-top-minor)) stack$c))
       (stack$c (maybe-resize-stack$c-frame-next-scratch (+ 1 new-top-minor) stack$c))
       (stack$c (update-stack$c-frame-next-scratchi top-minor (stack$c-next-scratch stack$c) stack$c))
       ;; (stack$c (update-stack$c-minori (+ 2 (* 3 new-top-minor)) 0 stack$c))
       )
    (update-stack$c-top-minor new-top-minor stack$c))
  ///
  (local (defthm hack2
           (implies (and (integerp a) (integerp b)
                         (<= a (+ 1 b))
                         (case-split (not (equal a (+ 1 b)))))
                    (<= a b))))

  (defret stack$c-okp-of-<fn>
    (implies (stack$c-okp stack$c)
             (stack$c-okp new-stack$c))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (member (car lit) '(stack$c-major-frames-welltyped
                                            stack$c-minor-frames-welltyped
                                            stack$c-major-frames-bounded
                                            stack$c-minor-frames-bounded
                                            stack$c-top-minor-ordered
                                            stack$c-scratch-codeslots-ok
                                            stack$c-next-scratch-ordered
                                            stack$c-next-scratch-bounded
                                            stack$c-top-minor-bounded
                                            stack$c-scratch-welltyped))
                        `(:expand (,lit)))))))

  (defthm stack$a-push-minor-frame-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$c-extract (stack$c-push-minor-frame stack$c))
                    (stack$a-push-minor-frame (stack$c-extract stack$c))))
    :hints(("Goal" :in-theory (enable stack$a-push-minor-frame
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      stack$c-build-major-frame
                                      ;; stack$c-build-minor-frames
                                      )
            :expand ((:free (next x)
                      (stack$c-build-minor-frame
                       (+ 1 (nth-nat *stack$c-top-minor1* stack$c)) next x))
                     (:free (bottom x)
                      (stack$c-build-minor-frames
                       bottom (nth-nat *stack$c-top-minor1* stack$c) x))
                     )))))



(define stack$c-set-bindings ((bindings fgl-object-bindings-p)
                              (stack$c stack$c-okp))
  :returns new-stack$c
  (b* ((top-major (stack$c-top-frame stack$c)))
    (update-stack$c-majori (* 3 top-major) (fgl-object-bindings-fix bindings) stack$c))
  ///
  
  (defret stack$c-okp-of-<fn>
    (implies (stack$c-okp stack$c)
             (stack$c-okp new-stack$c))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (member (car lit) '(stack$c-major-frames-welltyped
                                            stack$c-minor-frames-welltyped
                                            stack$c-major-frames-bounded
                                            stack$c-minor-frames-bounded
                                            stack$c-top-minor-ordered
                                            stack$c-scratch-codeslots-ok
                                            stack$c-next-scratch-ordered
                                            stack$c-next-scratch-bounded
                                            stack$c-top-minor-bounded
                                            stack$c-scratch-welltyped))
                        `(:expand (,lit)))))))

  

  (defthm stack$a-set-bindings-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$c-extract (stack$c-set-bindings bindings stack$c))
                    (stack$a-set-bindings bindings (stack$c-extract stack$c))))
    :hints(("Goal" :in-theory (enable stack$a-set-bindings
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      )))))



(define stack$c-add-binding ((var pseudo-var-p)
                             (val fgl-object-p)
                             (stack$c stack$c-okp))
  :returns new-stack$c
  (b* ((top-major (stack$c-top-frame stack$c))
       (index (* 3 top-major)))
    (update-stack$c-majori index (cons (cons (pseudo-var-fix var)
                                             (fgl-object-fix val))
                                       (stack$c-majori index stack$c))
                           stack$c))
  ///
  
  (defret stack$c-okp-of-<fn>
    (implies (stack$c-okp stack$c)
             (stack$c-okp new-stack$c))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (member (car lit) '(stack$c-major-frames-welltyped
                                            stack$c-minor-frames-welltyped
                                            stack$c-major-frames-bounded
                                            stack$c-minor-frames-bounded
                                            stack$c-top-minor-ordered
                                            stack$c-scratch-codeslots-ok
                                            stack$c-next-scratch-ordered
                                            stack$c-next-scratch-bounded
                                            stack$c-top-minor-bounded
                                            stack$c-scratch-welltyped))
                        `(:expand (,lit)))))))

  
  (defthm stack$a-add-binding-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$c-extract (stack$c-add-binding var val stack$c))
                    (stack$a-add-binding var val (stack$c-extract stack$c))))
    :hints(("Goal" :in-theory (enable stack$a-add-binding
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      )))))


;; (local (defthm plus-1-equal-*-2
;;          (implies (and (integerp x) (integerp y))
;;                   (not (equal (* 2 x) (+ 1 (* 2 y)))))
;;          :hints (("Goal" :use ((:theorem (implies (equal (* 2 x) (+ 1 (* 2 y))) (equal (fix x) (+ 1/2 (fix y))))))))))

(define stack$c-set-rule ((rule maybe-fgl-generic-rule-p)
                          (stack$c stack$c-okp))
  :returns new-stack$c
  (b* ((top-major (stack$c-top-frame stack$c)))
    (update-stack$c-majori (+ 1 (* 3 top-major)) (maybe-fgl-generic-rule-fix rule) stack$c))
  ///
  
  (defret stack$c-okp-of-<fn>
    (implies (stack$c-okp stack$c)
             (stack$c-okp new-stack$c))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (member (car lit) '(stack$c-major-frames-welltyped
                                            stack$c-minor-frames-welltyped
                                            stack$c-major-frames-bounded
                                            stack$c-minor-frames-bounded
                                            stack$c-top-minor-ordered
                                            stack$c-scratch-codeslots-ok
                                            stack$c-next-scratch-ordered
                                            stack$c-next-scratch-bounded
                                            stack$c-top-minor-bounded
                                            stack$c-scratch-welltyped))
                        `(:expand (,lit)))))))

  
  (defthm stack$a-set-rule-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$c-extract (stack$c-set-rule rule stack$c))
                    (stack$a-set-rule rule (stack$c-extract stack$c))))
    :hints(("Goal" :in-theory (enable stack$a-set-rule
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      )))))

(define stack$c-set-phase ((phase acl2::maybe-natp)
                           (stack$c stack$c-okp))
  :returns new-stack$c
  (b* ((top-major (stack$c-top-frame stack$c)))
    (update-stack$c-majori (+ 2 (* 3 top-major)) (acl2::maybe-natp-fix phase) stack$c))
  ///
  
  (defret stack$c-okp-of-<fn>
    (implies (stack$c-okp stack$c)
             (stack$c-okp new-stack$c))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (member (car lit) '(stack$c-major-frames-welltyped
                                            stack$c-minor-frames-welltyped
                                            stack$c-major-frames-bounded
                                            stack$c-minor-frames-bounded
                                            stack$c-top-minor-ordered
                                            stack$c-scratch-codeslots-ok
                                            stack$c-next-scratch-ordered
                                            stack$c-next-scratch-bounded
                                            stack$c-top-minor-bounded
                                            stack$c-scratch-welltyped))
                        `(:expand (,lit)))))))

  
  (defthm stack$a-set-phase-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$c-extract (stack$c-set-phase phase stack$c))
                    (stack$a-set-phase phase (stack$c-extract stack$c))))
    :hints(("Goal" :in-theory (enable stack$a-set-phase
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      )))))

(define stack$c-set-minor-bindings ((bindings fgl-object-bindings-p)
                                    (stack$c stack$c-okp))
  :guard-hints (("goal" :do-not-induct t))
  :returns new-stack$c
  (b* ((top-minor (stack$c-top-minor stack$c)))
    (update-stack$c-minori (* 3 top-minor)
                           (fgl-object-bindings-fix bindings)
                           stack$c))
  ///
  
  (defret stack$c-okp-of-<fn>
    (implies (stack$c-okp stack$c)
             (stack$c-okp new-stack$c))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (member (car lit) '(stack$c-major-frames-welltyped
                                            stack$c-minor-frames-welltyped
                                            stack$c-major-frames-bounded
                                            stack$c-minor-frames-bounded
                                            stack$c-top-minor-ordered
                                            stack$c-scratch-codeslots-ok
                                            stack$c-next-scratch-ordered
                                            stack$c-next-scratch-bounded
                                            stack$c-top-minor-bounded
                                            stack$c-scratch-welltyped))
                        `(:expand (,lit)))))))

  (defthm stack$a-set-minor-bindings-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$c-extract (stack$c-set-minor-bindings bindings stack$c))
                    (stack$a-set-minor-bindings bindings (stack$c-extract stack$c))))
    :hints(("Goal" :in-theory (enable stack$a-set-minor-bindings
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      stack$c-build-major-frame
                                      stack$c-build-minor-frame
                                      )
            :expand ((:free (bottom x)
                      (stack$c-build-minor-frames
                       bottom (nth-nat *stack$c-top-minor1* stack$c) x))
                     )))))

(define stack$c-add-minor-bindings ((bindings fgl-object-bindings-p)
                                    (stack$c stack$c-okp))
  :returns new-stack$c
  (b* ((top-minor (stack$c-top-minor stack$c))
       (index (* 3 top-minor)))
    (update-stack$c-minori index
                           (append (fgl-object-bindings-fix bindings) (stack$c-minori index stack$c))
                           stack$c))
  ///
  
  (defret stack$c-okp-of-<fn>
    (implies (stack$c-okp stack$c)
             (stack$c-okp new-stack$c))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (member (car lit) '(stack$c-major-frames-welltyped
                                            stack$c-minor-frames-welltyped
                                            stack$c-major-frames-bounded
                                            stack$c-minor-frames-bounded
                                            stack$c-top-minor-ordered
                                            stack$c-scratch-codeslots-ok
                                            stack$c-next-scratch-ordered
                                            stack$c-next-scratch-bounded
                                            stack$c-top-minor-bounded
                                            stack$c-scratch-welltyped))
                        `(:expand (,lit)))))))

  (defthm stack$a-add-minor-bindings-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$c-extract (stack$c-add-minor-bindings bindings stack$c))
                    (stack$a-add-minor-bindings bindings (stack$c-extract stack$c))))
    :hints(("Goal" :in-theory (enable stack$a-add-minor-bindings
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      stack$c-build-major-frame
                                      stack$c-build-minor-frame
                                      )
            :expand ((:free (bottom x)
                      (stack$c-build-minor-frames
                       bottom (nth-nat *stack$c-top-minor1* stack$c) x))
                     )))))

(define stack$c-set-term ((term pseudo-termp)
                          (stack$c stack$c-okp))
  :returns new-stack$c
  (b* ((top-minor (stack$c-top-minor stack$c)))
    (update-stack$c-minori (+ 1 (* 3 top-minor)) (pseudo-term-fix term) stack$c))
  ///
  
  (defret stack$c-okp-of-<fn>
    (implies (stack$c-okp stack$c)
             (stack$c-okp new-stack$c))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (member (car lit) '(stack$c-major-frames-welltyped
                                            stack$c-minor-frames-welltyped
                                            stack$c-major-frames-bounded
                                            stack$c-minor-frames-bounded
                                            stack$c-top-minor-ordered
                                            stack$c-scratch-codeslots-ok
                                            stack$c-next-scratch-ordered
                                            stack$c-next-scratch-bounded
                                            stack$c-top-minor-bounded
                                            stack$c-scratch-welltyped))
                        `(:expand (,lit)))))))

  (defthm stack$a-set-term-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$c-extract (stack$c-set-term term stack$c))
                    (stack$a-set-term term (stack$c-extract stack$c))))
    :hints(("Goal" :in-theory (enable stack$a-set-term
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      stack$c-build-major-frame
                                      stack$c-build-minor-frame
                                      )
            :expand ((:free (bottom x)
                      (stack$c-build-minor-frames
                       bottom (nth-nat *stack$c-top-minor1* stack$c) x))
                     )))))

(define stack$c-set-term-index ((term-index acl2::maybe-natp)
                                (stack$c stack$c-okp))
  :returns new-stack$c
  (b* ((top-minor (stack$c-top-minor stack$c)))
    (update-stack$c-minori (+ 2 (* 3 top-minor)) (acl2::maybe-natp-fix term-index) stack$c))
  ///
  
  (defret stack$c-okp-of-<fn>
    (implies (stack$c-okp stack$c)
             (stack$c-okp new-stack$c))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (member (car lit) '(stack$c-major-frames-welltyped
                                            stack$c-minor-frames-welltyped
                                            stack$c-major-frames-bounded
                                            stack$c-minor-frames-bounded
                                            stack$c-top-minor-ordered
                                            stack$c-scratch-codeslots-ok
                                            stack$c-next-scratch-ordered
                                            stack$c-next-scratch-bounded
                                            stack$c-top-minor-bounded
                                            stack$c-scratch-welltyped))
                        `(:expand (,lit)))))))

  (defthm stack$a-set-term-index-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$c-extract (stack$c-set-term-index term-index stack$c))
                    (stack$a-set-term-index term-index (stack$c-extract stack$c))))
    :hints(("Goal" :in-theory (enable stack$a-set-term-index
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      stack$c-build-major-frame
                                      stack$c-build-minor-frame
                                      )
            :expand ((:free (bottom x)
                      (stack$c-build-minor-frames
                       bottom (nth-nat *stack$c-top-minor1* stack$c) x))
                     )))))

(define stack$c-bindings ((stack$c stack$c-okp))
  (fgl-object-bindings-fix
   (stack$c-majori (* 3 (stack$c-top-frame stack$c)) stack$c))
  ///
  (defthm stack$a-bindings-of-stack$c-extract
    (equal (stack$a-bindings (stack$c-extract stack$c))
           (stack$c-bindings stack$c))
    :hints(("Goal" :in-theory (enable stack$a-bindings
                                      stack$c-extract
                                      stack$c-build-top-major-frame)))))

(define stack$c-nth-frame-bindings ((n natp)
                              (stack$c stack$c-okp))
  :guard (< n (stack$c-frames stack$c))
  :guard-hints (("goal" :in-theory (e/d (stack$c-frames)
                                        (stack$c-major-frames-welltyped-necc))
                 :use ((:instance stack$c-major-frames-welltyped-necc
                        (i (nfix (- (stack$c-top-frame stack$c) (nfix n))))))))
  (fgl-object-bindings-fix
    (stack$c-majori (* 3 (mbe :logic (nfix (- (stack$c-top-frame stack$c) (nfix n)))
                              :exec (- (stack$c-top-frame stack$c) n)))
                    stack$c))
  ///
  (local (defthm diff-equal-0
           (equal (equal (+ (- n) x) 0)
                  (equal (fix n) (fix x)))))

  (defthm stack$a-nth-frame-bindings-of-stack$c-extract
    (equal (stack$a-nth-frame-bindings n (stack$c-extract stack$c))
           (stack$c-nth-frame-bindings n stack$c))
    :hints(("Goal" :in-theory (enable stack$a-nth-frame-bindings
                                      stack$c-extract
                                      stack$a-frames
                                      stack$c-build-major-frame
                                      stack$c-build-top-major-frame
                                      max)
            :expand ((:free (n a b) (nth n (cons a b)))
                     (:free (a b) (len (cons a b))))))))

(define stack$c-nth-frame-minor-frames ((n natp)
                                        (stack$c stack$c-okp))
  :guard (< n (stack$c-frames stack$c))
  :guard-hints (("goal" :in-theory (e/d (stack$c-frames))))
  :guard-debug t
  (b* ((nframes (stack$c-frames stack$c))
       (n (mbe :logic (min (nfix n) (1- nframes))
               :exec n))
       (top-minor (if (eql n 0)
                      (stack$c-top-minor stack$c)
                    (stack$c-frame-top-minori (- nframes (+ 1 n)) stack$c)))
       (prev-minor (if (eql 0 (- nframes (+ 1 n)))
                       -1
                     (stack$c-frame-top-minori (- nframes (+ 2 n)) stack$c))))
    (- top-minor prev-minor))
  ///
  (local (defthm diff-equal-0
           (equal (equal (+ (- n) x) 0)
                  (equal (fix n) (fix x)))))

  (defthm stack$a-nth-frame-minor-frames-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$a-nth-frame-minor-frames n (stack$c-extract stack$c))
                    (stack$c-nth-frame-minor-frames n stack$c)))
    :hints(("Goal" :in-theory (enable stack$a-nth-frame-minor-frames
                                      stack$c-extract
                                      stack$a-frames
                                      stack$c-frames
                                      stack$c-build-major-frame
                                      stack$c-build-top-major-frame
                                      max)
            :expand ((:free (n a b) (nth n (cons a b)))
                     (:free (a b) (len (cons a b))))))))




(define stack$c-minor-bindings ((stack$c stack$c-okp))
  (b* ((top-minor (stack$c-top-minor stack$c))
       (index (* 3 top-minor)))
    (fgl-object-bindings-fix (stack$c-minori index stack$c)))
  ///
  (defthm stack$a-minor-bindings-of-stack$c-extract
    (equal (stack$a-minor-bindings (stack$c-extract stack$c))
           (stack$c-minor-bindings stack$c))
    :hints(("Goal" :in-theory (enable stack$a-minor-bindings
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      stack$c-build-minor-frame)))))

(define stack$c-nth-frame-minor-bindings ((n natp)
                                          (m natp)
                                          (stack$c stack$c-okp))
  :guard (and (< n (stack$c-frames stack$c))
              (< m (stack$c-nth-frame-minor-frames n stack$c)))
  :guard-hints (("goal" :in-theory (e/d (stack$c-frames
                                         stack$c-nth-frame-minor-frames)
                                        (stack$c-minor-frames-welltyped-necc))
                 :use ((:instance stack$c-minor-frames-welltyped-necc
                        (i (b* ((nframes (stack$c-frames stack$c))
                                (n (mbe :logic (min (nfix n) (1- nframes))
                                        :exec n))
                                (top-minor (if (eql n 0)
                                               (stack$c-top-minor stack$c)
                                             (stack$c-frame-top-minori (- nframes (+ 1 n)) stack$c)))
                                (m (mbe :logic (min (nfix m) (1- (stack$c-nth-frame-minor-frames n stack$c)))
                                        :exec m)))
                             (- top-minor m)))))
                 :do-not-induct t))
  :guard-debug t
  (b* ((nframes (stack$c-frames stack$c))
       (n (mbe :logic (min (nfix n) (1- nframes))
               :exec n))
       (top-minor (if (eql n 0)
                      (stack$c-top-minor stack$c)
                    (stack$c-frame-top-minori (- nframes (+ 1 n)) stack$c)))
       (m (mbe :logic (min (nfix m) (1- (stack$c-nth-frame-minor-frames n stack$c)))
               :exec m))
       (index (* 3 (- top-minor m))))
    (fgl-object-bindings-fix (stack$c-minori index stack$c)))
  ///
  (local (defthm diff-equal-0
           (equal (equal (+ (- n) x) 0)
                  (equal (fix n) (fix x)))))

  (defthm stack$a-nth-frame-minor-bindings-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$a-nth-frame-minor-bindings n m (stack$c-extract stack$c))
                    (stack$c-nth-frame-minor-bindings n m stack$c)))
    :hints(("Goal" :in-theory (e/d (stack$a-nth-frame-minor-bindings
                                    stack$a-nth-frame-minor-frames
                                    stack$c-nth-frame-minor-frames
                                    stack$c-extract
                                    stack$a-frames
                                    stack$c-frames
                                    stack$c-build-major-frame
                                    stack$c-build-minor-frame
                                    stack$c-build-top-major-frame
                                    max)
                                   (stack$c-minor-frames-welltyped-necc))
            :expand ((:free (n a b) (nth n (cons a b)))
                     (:free (a b) (len (cons a b))))))))


(define stack$c-rule ((stack$c stack$c-okp))
  (maybe-fgl-generic-rule-fix (stack$c-majori (+ 1 (* 3 (stack$c-top-frame stack$c))) stack$c))
  ///
  (defthm stack$a-rule-of-stack$c-extract
    (equal (stack$a-rule (stack$c-extract stack$c))
           (stack$c-rule stack$c))
    :hints(("Goal" :in-theory (enable stack$a-rule
                                      stack$c-extract
                                      stack$c-build-top-major-frame)))))

(define stack$c-phase ((stack$c stack$c-okp))
  (acl2::maybe-natp-fix (stack$c-majori (+ 2 (* 3 (stack$c-top-frame stack$c))) stack$c))
  ///
  (defthm stack$a-phase-of-stack$c-extract
    (equal (stack$a-phase (stack$c-extract stack$c))
           (stack$c-phase stack$c))
    :hints(("Goal" :in-theory (enable stack$a-phase
                                      stack$c-extract
                                      stack$c-build-top-major-frame)))))

(define stack$c-term ((stack$c stack$c-okp))
  (b* ((top-minor (stack$c-top-minor stack$c))
       (index (+ 1 (* 3 top-minor))))
    (pseudo-term-fix (stack$c-minori index stack$c)))
  ///
  (defthm stack$a-term-of-stack$c-extract
    (equal (stack$a-term (stack$c-extract stack$c))
           (stack$c-term stack$c))
    :hints(("Goal" :in-theory (enable stack$a-term
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      stack$c-build-minor-frame)))))

(define stack$c-term-index ((stack$c stack$c-okp))
  (b* ((top-minor (stack$c-top-minor stack$c))
       (index (+ 2 (* 3 top-minor))))
    (acl2::maybe-natp-fix (stack$c-minori index stack$c)))
  ///
  (defthm stack$a-term-index-of-stack$c-extract
    (equal (stack$a-term-index (stack$c-extract stack$c))
           (stack$c-term-index stack$c))
    :hints(("Goal" :in-theory (enable stack$a-term-index
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      stack$c-build-minor-frame)))))

(define stack$c-scratch-len ((stack$c stack$c-okp))

  (b* ((top-minor (stack$c-top-minor stack$c))
       (prev-scratch (if (eql top-minor 0)
                         1
                       (stack$c-frame-next-scratchi (+ -1 top-minor) stack$c))))
    (- (scratch-nontagidx-to-index (stack$c-next-scratch stack$c))
       (scratch-nontagidx-to-index prev-scratch)))
  ///
  (defthm stack$a-scratch-len-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$a-scratch-len (stack$c-extract stack$c))
                    (stack$c-scratch-len stack$c)))
    :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      stack$c-build-minor-frame)))))



(define stack$c-full-scratch-len ((stack$c stack$c-okp))
  (scratch-nontagidx-to-index (stack$c-next-scratch stack$c))
  ///
  (defthm stack$a-full-scratch-len-of-stack$c-extract
    (implies (stack$c-okp stack$c)
             (equal (stack$a-full-scratch-len (stack$c-extract stack$c))
                    (stack$c-full-scratch-len stack$c)))
    :hints(("Goal" :in-theory (enable stack$a-full-scratch-len
                                      major-stack-scratch-len
                                      minor-stack-scratch-len
                                      stack$c-extract
                                      stack$c-build-top-major-frame
                                      stack$c-build-minor-frame)))))


(define stack$c-top-scratch ((stack$c stack$c-okp))
  :guard-hints (("goal" :in-theory (e/d (stack$c-scratch-len))
                 :do-not-induct t))
  :guard-debug t
  :guard (< 0 (stack$c-scratch-len stack$c))
  (stack$c-scratch-entry
   (scratch-decr-nontagidx (stack$c-next-scratch stack$c))
   stack$c)
  ///
  (defthm stack$a-top-scratch-of-stack$c-extract
    (implies (and (stack$c-okp stack$c)
                  (< 0 (stack$c-scratch-len stack$c)))
             (equal (stack$a-top-scratch (stack$c-extract stack$c))
                    (stack$c-top-scratch stack$c)))
    :hints(("Goal" :in-theory (e/d (stack$a-top-scratch
                                    stack$c-scratch-len
                                    stack$c-extract
                                    stack$c-build-top-major-frame
                                    stack$c-build-minor-frame)
                                   (scratch-decr-nontagidx-in-terms-of-conversions))
            :expand ((:free (bottom)
                      (stack$c-build-scratch bottom
                                             (nth-nontag *stack$c-next-scratch1* stack$c)
                                             stack$c)))))))



(local (defthmd index-to-scratch-nontagidx->
         (implies (and ;; (syntaxp (quotep c))
                   (scratch-nontagidx-p c))
                  (iff (> c (index-to-scratch-nontagidx x))
                       (> (scratch-nontagidx-to-index c) (nfix x))))
         :hints (("Goal" :use index-to-scratch-nontagidx->-const))))

(local (defthmd index-to-scratch-nontagidx-<
         (implies (and ;; (syntaxp (quotep c))
                   (scratch-nontagidx-p c))
                  (iff (< c (index-to-scratch-nontagidx x))
                       (< (scratch-nontagidx-to-index c) (nfix x))))
         :hints (("Goal" :use index-to-scratch-nontagidx-<-const))))

(define stack$c-nth-scratch ((n natp)
                             (stack$c stack$c-okp))
  :guard-hints (("goal" :in-theory (e/d (stack$c-full-scratch-len
                                         index-to-scratch-nontagidx->))
                 :do-not-induct t))
  :guard-debug t
  :guard (< n (stack$c-full-scratch-len stack$c))
  (stack$c-scratch-entry
   (scratch-nontagidx-offset (stack$c-next-scratch stack$c) (+ -1 (- (lnfix n))))
   stack$c)
  ///
  ;; (local (defun nth-of-build-scratch-ind (n top bottom)
  ;;          (if (zp n)
  ;;              (list top bottom)
  ;;            (nth-of-build-scratch-ind (1- n) (scratch-decr-nontagidx top) bottom))))
  ;; (local (defthm nth-of-stack$c-build-scratch
  ;;          (implies (< (nfix n) (- (scratch-nontagidx-to-index top)
  ;;                                  (scratch-nontagidx-to-index bottom)))
  ;;                   (equal (nth n (stack$c-build-scratch bottom top stack$c))
  ;;                          (stack$c-scratch-entry
  ;;                           (scratch-nontagidx-offset top (+ -1 (- (nfix n))))
  ;;                           stack$c)))
  ;;          :hints(("Goal" :in-theory (enable nth)
  ;;                  :induct (nth-of-build-scratch-ind n top bottom)
  ;;                  :expand ((stack$c-build-scratch bottom top stack$c)))
  ;;                 (and stable-under-simplificationp
  ;;                      '(:use ((:instance scratch-nontagidx-to-index-monotonic
  ;;                               (x bottom) (y top)))
  ;;                        :in-theory (disable scratch-nontagidx-to-index-monotonic))))))

  (defthm stack$a-nth-scratch-of-stack$c-extract
    (implies (and (stack$c-okp stack$c)
                  (< (nfix n) (stack$c-full-scratch-len stack$c)))
             (equal (stack$a-nth-scratch n (stack$c-extract stack$c))
                    (stack$c-nth-scratch n stack$c)))
    :hints(("Goal" :in-theory (e/d (stack$a-nth-scratch
                                    stack$c-full-scratch-len
                                    ;; stack$c-extract
                                    stack$c-build-top-major-frame
                                    stack$c-build-minor-frame)
                                   (scratch-decr-nontagidx-in-terms-of-conversions))))))


(define stack$c-nth-scratch-kind ((n natp)
                                  (stack$c stack$c-okp))
  :guard-hints (("goal" :in-theory (e/d (stack$c-full-scratch-len
                                         index-to-scratch-nontagidx->
                                         index-to-scratch-nontagidx-<))
                 :do-not-induct t))
  :guard-debug t
  :guard (< n (stack$c-full-scratch-len stack$c))
  (scratchobj-code->kind
   (scratch-entry-kindcode
    (scratch-nontagidx-offset (stack$c-next-scratch stack$c) (+ -1 (- (lnfix n))))
    stack$c))
  ///
  (local (defthm scratchobj-kind-of-stack$c-scratch-entry
           (equal (scratchobj-kind (stack$c-scratch-entry n stack$c))
                  (scratchobj-code->kind (scratch-entry-kindcode (scratch-nontagidx-fix n) stack$c)))
           :hints(("Goal" :in-theory (enable stack$c-scratch-entry)))))

  ;; (local (defun nth-of-build-scratch-ind (n top bottom)
  ;;          (if (zp n)
  ;;              (list top bottom)
  ;;            (nth-of-build-scratch-ind (1- n) (scratch-decr-nontagidx top) bottom))))
  ;; (local (defthm nth-of-stack$c-build-scratch
  ;;          (implies (< (nfix n) (- (scratch-nontagidx-to-index top)
  ;;                                  (scratch-nontagidx-to-index bottom)))
  ;;                   (equal (nth n (stack$c-build-scratch bottom top stack$c))
  ;;                          (stack$c-scratch-entry
  ;;                           (scratch-nontagidx-offset top (+ -1 (- (nfix n))))
  ;;                           stack$c)))
  ;;          :hints(("Goal" :in-theory (enable nth)
  ;;                  :induct (nth-of-build-scratch-ind n top bottom)
  ;;                  :expand ((stack$c-build-scratch bottom top stack$c)))
  ;;                 (and stable-under-simplificationp
  ;;                      '(:use ((:instance scratch-nontagidx-to-index-monotonic
  ;;                               (x bottom) (y top)))
  ;;                        :in-theory (disable scratch-nontagidx-to-index-monotonic))))))

  (defthm stack$a-nth-scratch-kind-of-stack$c-extract
    (implies (and (stack$c-okp stack$c)
                  (< (nfix n) (stack$c-full-scratch-len stack$c)))
             (equal (stack$a-nth-scratch-kind n (stack$c-extract stack$c))
                    (stack$c-nth-scratch-kind n stack$c)))
    :hints(("Goal" :in-theory (e/d (stack$a-nth-scratch-kind
                                    stack$c-full-scratch-len
                                    ;; stack$c-extract
                                    stack$c-build-top-major-frame
                                    stack$c-build-minor-frame)
                                   (scratch-decr-nontagidx-in-terms-of-conversions))))))


(local (defthm stack$c-okp-of-maybe-resize-stack$c-scratch
         (implies (stack$c-okp stack$c)
                  (stack$c-okp
                   (update-nth *stack$c-scratchi1*
                               (maybe-grow-list
                                n 0
                                (nth *stack$c-scratchi1* stack$c))
                               stack$c)))
         :hints ((and stable-under-simplificationp
                      (let ((lit (car (last clause))))
                        (and (member (car lit) '(stack$c-major-frames-welltyped
                                                 stack$c-minor-frames-welltyped
                                                 stack$c-major-frames-bounded
                                                 stack$c-minor-frames-bounded
                                                 stack$c-top-minor-ordered
                                                 stack$c-scratch-codeslots-ok
                                                 stack$c-next-scratch-ordered
                                                 stack$c-next-scratch-bounded
                                                 stack$c-top-minor-bounded
                                                 stack$c-scratch-welltyped))
                             `(:expand (,lit))))))))



(define stack$c-push-scratch ((obj scratchobj-p)
                              (stack$c stack$c-okp))
  :returns (new-stack$c)
  :guard-debug t
  :guard-hints (("goal" :do-not-induct t
                 :use ((:instance stack$c-okp-of-maybe-resize-stack$c-scratch
                        (n (+ 1 (scratch-incr-nontagidx (stack$c-next-scratch stack$c))))))
                 :in-theory (disable stack$c-okp-of-maybe-resize-stack$c-scratch))
                )
  :prepwork ((local (in-theory (enable len-of-update-nth-scratch
                                       stack$c-scratch-welltyped-casesplit))))
  (b* ((next (stack$c-next-scratch stack$c))
       (next-next (scratch-incr-nontagidx next))
       (stack$c (maybe-resize-stack$c-scratch (+ 1 next-next) stack$c))
       (stack$c (update-stack$c-scratch-entry next obj stack$c)))
    (update-stack$c-next-scratch next-next stack$c))
  ///
  (local (defthm stack$c-okp-of-update-stack$c-next-scratch
           (implies (and (stack$c-okp stack$c)
                         (equal next (scratch-incr-nontagidx
                                      (stack$c-next-scratch stack$c)))
                         (scratchobj-code/val-okp
                          (scratch-entry-kindcode (stack$c-next-scratch stack$c) stack$c)
                          (nth-scratch (stack$c-next-scratch stack$c)
                                       (nth *stack$c-scratchi1* stack$c)))
                         (< next (len (nth *stack$c-scratchi1* stack$c))))
                    (stack$c-okp (update-stack$c-next-scratch next stack$c)))
           :hints ((and stable-under-simplificationp
                        (let ((lit (car (last clause))))
                          (and (member (car lit) '(stack$c-major-frames-welltyped
                                                   stack$c-minor-frames-welltyped
                                                   stack$c-major-frames-bounded
                                                   stack$c-minor-frames-bounded
                                                   stack$c-top-minor-ordered
                                                   stack$c-scratch-codeslots-ok
                                                   stack$c-next-scratch-ordered
                                                   stack$c-next-scratch-bounded
                                                   stack$c-top-minor-bounded
                                                   stack$c-scratch-welltyped))
                               `(:expand (,lit))))))))
           



  (defret stack$c-okp-of-<fn>
    (implies (stack$c-okp stack$c)
             (stack$c-okp new-stack$c))
    :hints(("Goal" :in-theory (disable stack$c-okp
                                       update-stack$c-next-scratch))))

  (defret stack$c-extract-of-<fn>
    (implies (stack$c-okp stack$c)
             (equal (stack$c-extract new-stack$c)
                    (stack$a-push-scratch obj (stack$c-extract stack$c))))
    :hints (("goal" :in-theory (e/d (stack$c-extract
                                     stack$c-build-top-major-frame
                                     stack$c-build-minor-frame
                                     stack$a-push-scratch)
                                    (scratch-incr-nontagidx-in-terms-of-conversions
                                     scratch-decr-nontagidx-in-terms-of-conversions))
             :expand
             ((:free (x)
               (stack$c-build-major-frames (nth-nat *stack$c-top-frame1* stack$c)
                                           x))
              (:free (x bottom)
               (stack$c-build-minor-frames bottom
                                           (nth-nat *stack$c-top-minor1* stack$c)
                                           x))
              (:free (x bottom)
               (stack$c-build-scratch
                bottom
                (scratch-incr-nontagidx (NTH-NONTAG *stack$c-next-scratch1* STACK$C))
                x))
              (:free (x)
               (stack$c-scratch-entry
                (nth-nontag *stack$c-next-scratch1* stack$c) x))
              (:free (x)
               (stack$c-scratch-entry 1 x)))
             :cases ((zp (SCRATCH-NONTAGIDX-TO-INDEX (NTH-NONTAG 7 STACK$C))))))))
                  

(local (defthm stack$c-top-minor-0-when-stack$c-okp
         (implies (equal 0 (nth-nat *stack$c-top-minor1* stack$c))
                  (equal (stack$c-top-minor-bounded limit stack$c)
                         (zp limit)))
         :hints (("goal" :use ((:instance stack$c-top-minor-bounded-necc
                                (j 0)))
                  :expand ((stack$c-top-minor-bounded limit stack$c))
                  :in-theory (disable stack$c-top-minor-bounded-necc)))))



(define stack$c-update-scratch ((n natp)
                                (obj scratchobj-p)
                                (stack$c stack$c-okp))
  :guard-hints (("goal" :in-theory (e/d (stack$c-scratch-len
                                         index-to-scratch-nontagidx-<))
                 :do-not-induct t))
  :guard-debug t
  :guard (< n (stack$c-scratch-len stack$c))
  :returns new-stack$c
  (update-stack$c-scratch-entry
   (scratch-nontagidx-offset (stack$c-next-scratch stack$c) (+ -1 (- (lnfix n))))
   obj
   stack$c)
  ///

  (defret stack$c-okp-of-<fn>
    (implies (stack$c-okp stack$c)
             (stack$c-okp new-stack$c))
    :hints(("Goal" :in-theory (disable stack$c-okp))))
             

  (local (defthm scratch-nontagidx-to-index-monotonic-linear
           (implies (< (scratch-nontagidx-fix x) (scratch-nontagidx-fix y))
                    (< (scratch-nontagidx-to-index x) (scratch-nontagidx-to-index y)))
           :rule-classes :linear))


  (local (defthm equal-of-index-to-scratch-nontagidx
           (implies (scratch-nontagidx-p x)
                    (equal (equal x (index-to-scratch-nontagidx y))
                           (equal (scratch-nontagidx-to-index x) (nfix y))))
           :hints (("goal" :use ((:instance index-to-scratch-nontagidx-equal
                                  (x (scratch-nontagidx-to-index x))
                                  (y (nfix y))))))))

  (local (defthm stack$c-build-scratch-of-update-stack$c-scratch-entry
           (implies (and (< (scratch-nontagidx-fix n) (scratch-nontagidx-fix top))
                         (<= (scratch-nontagidx-fix bottom) (scratch-nontagidx-fix n)))
                    (equal (stack$c-build-scratch bottom top
                                                  (update-stack$c-scratch-entry n obj stack$c))
                           (update-nth (+ -1 (- (scratch-nontagidx-to-index top)
                                                (scratch-nontagidx-to-index n)))
                                       (scratchobj-fix obj)
                                       (stack$c-build-scratch bottom top stack$c))))
           :hints (("goal" :induct (stack$c-build-scratch bottom top stack$c)
                    :in-theory (enable (:i stack$c-build-scratch)
                                       update-nth
                                       index-to-scratch-nontagidx-<)
                    :expand ((:free (x) (stack$c-build-scratch bottom top x)))))))

  (local (in-theory (enable INDEX-TO-SCRATCH-NONTAGIDX->
                            INDEX-TO-SCRATCH-NONTAGIDX-<)))

  (local (defthm stack$c-next-scratch-ordered-lemma2
           (implies (and (stack$c-next-scratch-ordered (nth-nat *stack$c-top-minor1* stack$c) stack$c)
                         (natp i)
                         (<= i (+ -1 (nth-nat *stack$c-top-minor1* stack$c))))
                    (<= (scratch-nontagidx-to-index
                         (nth-nontag i (nth *stack$c-frame-next-scratchi1* stack$c)))
                        (scratch-nontagidx-to-index
                         (nth-nontag (+ -1 (nth-nat *stack$c-top-minor1* stack$c)) (nth *stack$c-frame-next-scratchi1* stack$c)))))
           :rule-classes :linear))

  (defthm stack$c-extract-of-<fn>
    (implies (and (stack$c-okp stack$c)
                  (< (nfix n) (stack$c-scratch-len stack$c)))
             (equal (stack$c-extract (stack$c-update-scratch n obj stack$c))
                    (stack$a-update-scratch n obj (stack$c-extract stack$c))))
    :hints(("Goal" :in-theory (e/d (stack$a-update-scratch
                                    stack$c-scratch-len
                                    stack$c-extract
                                    stack$c-build-top-major-frame
                                    stack$c-build-minor-frame))))))



(define stack$c-pop-scratch ((stack$c stack$c-okp))
  :guard (< 0 (stack$c-scratch-len stack$c))
  :returns (new-stack$c)
  :guard-debug t
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable stack$c-scratch-len)))
  :prepwork ((local (in-theory (enable len-of-update-nth-scratch
                                       stack$c-scratch-welltyped-casesplit))))
  (b* ((next (stack$c-next-scratch stack$c))
       (next-next (scratch-decr-nontagidx next))
       (stack$c (update-stack$c-scratchi next-next 0 stack$c)))
    (update-stack$c-next-scratch next-next stack$c))
  ///

  (local (defthm stack$c-scratch-len-implies-decr-nontagidx-bound
           (implies (and (< 0 (stack$c-scratch-len stack$c))
                         (stack$c-next-scratch-ordered (stack$c-top-minor stack$c) stack$c)
                         (< (nfix n) (stack$c-top-minor stack$c)))
                    ;; (b* ((top-minor (stack$c-top-minor stack$c)))
                    (<= (nth-nontag n (nth *stack$c-frame-next-scratchi1* stack$c))
                        (scratch-decr-nontagidx (nth-nontag *stack$c-next-scratch1* stack$c))))
           :hints(("Goal" :in-theory (e/d (stack$c-scratch-len
                                           index-to-scratch-nontagidx->
                                           nfix)
                                          (stack$c-next-scratch-ordered-necc
                                           scratch-nontagidx-to-index-monotonic))
                   :use ((:instance stack$c-next-scratch-ordered-necc
                          (limit (stack$c-top-minor stack$c))
                          (j (+ -1 (stack$c-top-minor stack$c)))
                          (i (nfix n)))
                         (:instance scratch-nontagidx-to-index-monotonic
                          (x (nth-nontag (+ -1 (stack$c-top-minor stack$c))
                                         (nth *stack$c-frame-next-scratchi1* stack$c)))
                          (y (nth-nontag n (nth *stack$c-frame-next-scratchi1* stack$c)))))))))

  (local (defthm stack$c-scratch-len-implies-decr-nontagidx-bound-2
           (implies (and (< 0 (stack$c-scratch-len stack$c))
                         (stack$c-next-scratch-ordered (stack$c-top-minor stack$c) stack$c)
                         (< (nfix n) (stack$c-top-minor stack$c)))
                    ;; (b* ((top-minor (stack$c-top-minor stack$c)))
                    (< (nth-nontag n (nth *stack$c-frame-next-scratchi1* stack$c))
                       (nth-nontag *stack$c-next-scratch1* stack$c)))
           :hints (("goal" :use stack$c-scratch-len-implies-decr-nontagidx-bound
                    :in-theory (enable stack$c-scratch-len)))))
  

  (defret stack$c-okp-of-<fn>
    (implies (and (stack$c-okp stack$c)
                  (< 0 (stack$c-scratch-len stack$c)))
             (stack$c-okp new-stack$c))
    :hints (("goal" :in-theory (e/d (;; stack$c-scratch-len
                                     )
                                    (scratch-decr-nontagidx-in-terms-of-conversions)))
            (and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (member (car lit) '(stack$c-major-frames-welltyped
                                            stack$c-minor-frames-welltyped
                                            stack$c-major-frames-bounded
                                            stack$c-minor-frames-bounded
                                            stack$c-top-minor-ordered
                                            stack$c-scratch-codeslots-ok
                                            stack$c-next-scratch-ordered
                                            stack$c-next-scratch-bounded
                                            stack$c-top-minor-bounded
                                            stack$c-scratch-welltyped))
                        `(:expand (,lit)))))
            (and stable-under-simplificationp
                 '(:cases ((equal (NTH-NONTAG (+ -1 (NTH-NAT 6 STACK$C))
                                              (NTH *STACK$C-FRAME-NEXT-SCRATCHI1* STACK$C))
                                  (stack$c-next-scratch stack$c)))))
            
            ;; (and stable-under-simplificationp
            ;;      '(:in-theory (enable index-to-scratch-nontagidx->)))
            ))

  (local (defthm stack$c-build-scratch-of-less
           (implies (<= (scratch-nontagidx-fix next) (scratch-nontagidx-fix bottom))
                    (equal (stack$c-build-scratch bottom next stack$c) nil))
           :hints(("Goal" :in-theory (enable stack$c-build-scratch)))))

  (defret stack$c-extract-of-<fn>
    (implies (and (stack$c-okp stack$c)
                  (< 0 (stack$c-scratch-len stack$c)))
             (equal (stack$c-extract new-stack$c)
                    (stack$a-pop-scratch (stack$c-extract stack$c))))
    :hints (("goal" :in-theory (e/d (stack$c-extract
                                     stack$c-build-top-major-frame
                                     stack$c-build-minor-frame
                                     stack$a-pop-scratch)
                                    (scratch-incr-nontagidx-in-terms-of-conversions
                                     scratch-decr-nontagidx-in-terms-of-conversions))
             :expand ((:free (bottom)
                       (stack$c-build-scratch
                        bottom (nth-nontag *stack$c-next-scratch1* stack$c) stack$c)))))))

;; (local (defthm scratch-nontagidx-offset-decr
;;          (implies (<= (ifix k) 0)
;;                   (<= (scratch-nontagidx-offset x k) (scratch-nontagidx-fix x)))
;;          :hints (("goal" :use ((:instance index-to-scratch-nontagidx-<-const
;;                                 (c (scratch-nontagidx-fix x))
;;                                 (x (+ (ifix k) (scratch-nontagidx-to-index x)))))))
;;          :rule-classes :linear))

(local (defthm scratch-nontagidx-offset-decr-strict
         (implies (and (< (ifix k) 0)
                       (< 0 (scratch-nontagidx-to-index x)))
                  (< (scratch-nontagidx-offset x k) (scratch-nontagidx-fix x)))
         :hints (("goal" :use ((:instance index-to-scratch-nontagidx->-const
                                (c (scratch-nontagidx-fix x))
                                (x (+ (ifix k) (scratch-nontagidx-to-index x)))))))
         :rule-classes :linear))

(local (defthm scratch-nontagidx-offset-decr-strict-rw
         (implies (and (< (ifix k) 0)
                       (< 0 (scratch-nontagidx-to-index x))
                       (<= (scratch-nontagidx-fix x) y))
                  (< (scratch-nontagidx-offset x k) y))))

;; (local (defthm scratch-nontagidx-offset-not-equal-rw
;;          (implies (and (< (ifix k) 0)
;;                        (< 0 (scratch-nontagidx-to-index x))
;;                        (<= (scratch-nontagidx-fix x) y))
;;                   (not (equal (scratch-nontagidx-offset x k) y)))))



;; (local (defthm posp-when-greater-than-natp
;;          (implies (and (< n x)
;;                        (natp n)
;;                        (integerp x))
;;                   (posp x))
;;          :rule-classes :forward-chaining))

;; (local (defthm posp-scratch-nontagidx-to-index-forward
;;          (implies (posp (scratch-nontagidx-to-index x))
;;                   (and (integerp x)
;;                        (<= 2 x)))
;;          :hints ((and stable-under-simplificationp
;;                       '(:in-theory (enable scratch-nontagidx-fix))))
;;          :rule-classes :forward-chaining))

(local (defthm unsigned-byte-p-of-scratch-nontagidx-offset
         (implies (and (unsigned-byte-p m x)
                       (scratch-nontagidx-p x)
                       (<= (ifix n) 0)
                       (posp m))
                  (unsigned-byte-p m (scratch-nontagidx-offset x n)))
         :hints(("Goal" :in-theory (e/d (unsigned-byte-p)
                                        (scratch-nontagidx-offset-in-terms-of-conversions
                                         scratch-nontagidx-offset-decr-strict-rw
                                         scratch-nontagidx-offset-decr-strict))
                 :use ((:instance scratch-nontagidx-offset-decr-strict
                        (k n))))
                (and stable-under-simplificationp
                     '(:in-theory (enable scratch-nontagidx-offset-in-terms-of-conversions))))))
                  


(local
 (defconst *scratchobj-push/top-template*
   '(progn
      (define stack$c-push-scratch-<kind> ((obj <pred>)
                                           (stack$c stack$c-okp))
        :returns (new-stack$c)
        :guard-debug t
        :guard-hints (("goal" :do-not-induct t
                       :in-theory (enable stack$c-push-scratch
                                          update-stack$c-scratch-entry)))
        :prepwork ((local (in-theory (enable len-of-update-nth-scratch
                                             stack$c-scratch-welltyped-casesplit))))
        :enabled t
        (mbe :logic (stack$c-push-scratch (scratchobj-<kind> obj) stack$c)
             :exec
             (b* ((next (stack$c-next-scratch stack$c))
                  (next-next (scratch-incr-nontagidx next))
                  (stack$c (maybe-resize-stack$c-scratch (+ 1 next-next) stack$c))
                  (stack$c (update-stack$c-scratchi next
                                                    (:@ :no-pred obj)
                                                    (:@ (not :no-pred) (<fix> obj))
                                                    stack$c))
                  (stack$c (update-scratch-entry-kindcode next (scratchobj-kind->code :<kind>) stack$c)))
               (update-stack$c-next-scratch next-next stack$c))))

      (define stack$c-top-scratch-<kind> ((stack$c stack$c-okp))
        :guard (and (< 0 (stack$c-scratch-len stack$c))
                    (scratchobj-case (stack$c-top-scratch stack$c) :<kind>))
        :guard-hints (("goal" :in-theory (enable stack$c-scratch-len
                                                 stack$c-top-scratch
                                                 stack$c-scratch-entry)
                       :do-not-induct t))
        :enabled t
        (mbe :logic
             (scratchobj-<kind>->val (stack$c-top-scratch stack$c))
             :exec
             (:@ :no-pred (stack$c-scratchi (scratch-decr-nontagidx (stack$c-next-scratch stack$c))
                                            stack$c))
             (:@ (not :no-pred)
              (<fix> (stack$c-scratchi (scratch-decr-nontagidx (stack$c-next-scratch stack$c))
                                       stack$c)))))

      (define stack$c-nth-scratch-<kind> ((n natp)
                                          (stack$c stack$c-okp))
        :guard (and (< n (stack$c-full-scratch-len stack$c))
                    (scratchobj-case (stack$c-nth-scratch n stack$c) :<kind>))
        :guard-hints (("goal" :in-theory (e/d (stack$c-full-scratch-len
                                                 stack$c-nth-scratch
                                                 stack$c-scratch-entry)
                                              (scratch-nontagidx-offset-in-terms-of-conversions))
                       :do-not-induct t))
        :enabled t
        (mbe :logic (scratchobj-<kind>->val (stack$c-nth-scratch n stack$c))
             :exec
             (:@ :no-pred (stack$c-scratchi (scratch-nontagidx-offset (stack$c-next-scratch stack$c)
                                                                      (1- (- (lnfix n))))
                                            stack$c))
             (:@ (not :no-pred)
              (<fix> (stack$c-scratchi (scratch-nontagidx-offset (stack$c-next-scratch stack$c)
                                                                 (1- (- (lnfix n))))
                                       stack$c)))))

      (define stack$c-update-scratch-<kind> ((n natp)
                                             (obj <pred>)
                                             (stack$c stack$c-okp))
        :guard-hints (("goal" :in-theory (e/d (stack$c-scratch-len
                                               index-to-scratch-nontagidx-<
                                               stack$c-update-scratch
                                               update-stack$c-scratch-entry
                                               len-of-update-nth-scratch)
                                              (scratch-nontagidx-offset-in-terms-of-conversions))
                       :do-not-induct t))
        :guard-debug t
        :guard (< n (stack$c-scratch-len stack$c))
        :returns new-stack$c
        :enabled t
        (mbe :logic
             (stack$c-update-scratch n (scratchobj-<kind> obj) stack$c)
             :Exec
             (b* ((idx (scratch-nontagidx-offset (stack$c-next-scratch stack$c) (+ -1 (- (lnfix n)))))
                  (stack$c (update-stack$c-scratchi idx
                                                    (:@ :no-pred obj) (:@ (not :no-pred) (<fix> obj))
                                                    stack$c)))
               (update-scratch-entry-kindcode idx <code> stack$c))))


        (define stack$c-pop-scratch-<kind> ((stack$c stack$c-okp))
          :guard (and (< 0 (stack$c-scratch-len stack$c))
                      (scratchobj-case (stack$c-top-scratch stack$c) :<kind>))
          :guard-hints (("goal" :in-theory (enable stack$c-scratch-len
                                                   stack$c-top-scratch-<kind>
                                                   stack$c-top-scratch
                                                   stack$c-pop-scratch
                                                   stack$c-scratch-entry)
                         :do-not-induct t))
          :enabled t
          (mbe :logic (b* ((obj (stack$c-top-scratch-<kind> stack$c))
                           (stack$c (stack$c-pop-scratch stack$c)))
                        (mv obj stack$c))
               :exec
               (b* ((next (stack$c-next-scratch stack$c))
                    (next-next (scratch-decr-nontagidx next))
                    (obj (stack$c-scratchi next-next stack$c))
                    (stack$c (update-stack$c-scratchi next-next 0 stack$c))
                    (stack$c (update-stack$c-next-scratch next-next stack$c)))
                 (mv 
                  (:@ :no-pred obj)
                  (:@ (not :no-pred)
                   (<fix> obj))
                  stack$c)))))))

(local (in-theory (disable acl2::nth-when-too-large-cheap
                           acl2::loghead-identity
                           scratch-nontagidx-p-when-loghead
                           member-equal)))

(make-event
 `(progn
    . ,(acl2::template-proj
        *scratchobj-push/top-template*
        *scratchobj-tmplsubsts*)))





(define stack$c-pop-minor-frame ((stack$c stack$c-okp))
  :guard (and (< 1 (stack$c-minor-frames stack$c))
              (eql (stack$c-scratch-len stack$c) 0))
  :guard-hints (("goal" :in-theory (enable stack$c-minor-frames)))
  :returns (new-stack$c)
  (b* ((top-minor (stack$c-top-minor stack$c))
       (offset (* 3 top-minor))
       (stack$c (update-stack$c-minori offset nil stack$c))
       (stack$c (update-stack$c-minori (+ 1 offset) nil stack$c))
       (stack$c (update-stack$c-minori (+ 2 offset) nil stack$c))
       (new-top-minor (+ -1 top-minor)))
    (update-stack$c-top-minor new-top-minor stack$c))
  ///
  (local (defthm top-minor-ordered-implies-not-equal
           (implies (and (stack$c-top-minor-ordered (stack$c-top-frame stack$c) stack$c)
                         (< 1 (- (stack$c-top-minor stack$c)
                                 (stack$c-frame-top-minori (+ -1 (stack$c-top-frame stack$c)) stack$c)))
                         (< (nfix n) (stack$c-top-frame stack$c)))
                    (and ;; (< (nth-nat n (nth *stack$c-frame-top-minori1* stack$c))
                         ;;    (+ -1 (nth-nat *stack$c-top-minor1* stack$c)))
                         (not (equal (nth-nat n (nth *stack$c-frame-top-minori1* stack$c))
                                     (+ -1 (nth-nat *stack$c-top-minor1* stack$c))))))
           :hints (("goal" :use ((:instance stack$c-top-minor-ordered-necc
                                  (i (nfix n)) (j (+ -1 (stack$c-top-frame stack$c)))
                                  (limit (stack$c-top-frame stack$c))))))))
                    

  (defret stack$c-okp-of-<fn>
    (implies (and (stack$c-okp stack$c)
                  (< 1 (stack$c-minor-frames stack$c))
                  (eql (stack$c-scratch-len stack$c) 0))
             (stack$c-okp new-stack$c))
    :hints (("goal" :in-theory (e/d (stack$c-scratch-len stack$c-minor-frames)))
            (and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (member (car lit) '(stack$c-major-frames-welltyped
                                            stack$c-minor-frames-welltyped
                                            stack$c-major-frames-bounded
                                            stack$c-minor-frames-bounded
                                            stack$c-top-minor-ordered
                                            stack$c-scratch-codeslots-ok
                                            stack$c-next-scratch-ordered
                                            stack$c-next-scratch-bounded
                                            stack$c-top-minor-bounded
                                            stack$c-scratch-welltyped))
                        `(:expand (,lit)))))))

  (defret stack$c-extract-of-<fn>
    (implies (and (stack$c-okp stack$c)
                  (< 1 (stack$c-minor-frames stack$c))
                  (eql (stack$c-scratch-len stack$c) 0))
             (equal (stack$c-extract new-stack$c)
                    (stack$a-pop-minor-frame (stack$c-extract stack$c))))
    :hints (("goal" :in-theory (e/d (stack$c-extract
                                     stack$c-build-top-major-frame
                                     stack$c-build-minor-frame
                                     stack$a-pop-minor-frame
                                     stack$c-scratch-len
                                     stack$c-minor-frames)
                                    (scratch-incr-nontagidx-in-terms-of-conversions
                                     scratch-decr-nontagidx-in-terms-of-conversions))
             :expand ((:free (n) (stack$c-build-minor-frames n n stack$c))
                      (:free (n) (stack$c-build-minor-frames n (+ -1 (nth-nat *stack$c-top-minor1* stack$c)) stack$c)))))))



(define stack$c-pop-frame ((stack$c stack$c-okp))
  :guard (and (< 1 (stack$c-frames stack$c))
              (eql 1 (stack$c-minor-frames stack$c))
              (eql 0 (stack$c-scratch-len stack$c)))
  ;; :prepwork ((local (defthm nth-nat-upper-bound-by-nth-dumb
  ;;                     (implies (and (< (nth n x) b)
  ;;                                   (posp b))
  ;;                              (< (+ -1 (nth-nat n x)) b))
  ;;                     :hints(("Goal" :in-theory (enable nth-nat nfix))))))
  :guard-hints (("goal" :in-theory (enable stack$c-frames stack$c-minor-frames)))
  :returns (new-stack$c)
  (b* ((top-major (stack$c-top-frame stack$c))
       (top-minor (stack$c-top-minor stack$c))
       (minor-offset (* 3 top-minor))
       (stack$c (update-stack$c-minori minor-offset nil stack$c))
       (stack$c (update-stack$c-minori (+ 1 minor-offset) nil stack$c))
       (stack$c (update-stack$c-minori (+ 2 minor-offset) nil stack$c))
       (major-offset (* 3 top-major))
       (stack$c (update-stack$c-majori major-offset nil stack$c))
       (stack$c (update-stack$c-majori (+ 1 major-offset) nil stack$c))
       (stack$c (update-stack$c-majori (+ 2 major-offset) nil stack$c))
       (stack$c (update-stack$c-top-frame (+ -1 top-major) stack$c)))
    (update-stack$c-top-minor (+ -1 top-minor) stack$c))
  ///
  
  
  (local (defthm top-minor-ordered-implies-not-equal
           (implies (and (stack$c-top-minor-ordered (stack$c-top-frame stack$c) stack$c)
                         (equal 1 (- (stack$c-top-minor stack$c)
                                     (stack$c-frame-top-minori (+ -1 (stack$c-top-frame stack$c)) stack$c)))
                         (< (nfix n) (+ -1 (stack$c-top-frame stack$c))))
                    (and ;; (< (nth-nat n (nth *stack$c-frame-top-minori1* stack$c))
                         ;;    (+ -1 (nth-nat *stack$c-top-minor1* stack$c)))
                         (not (equal (nth-nat n (nth *stack$c-frame-top-minori1* stack$c))
                                     (+ -1 (nth-nat *stack$c-top-minor1* stack$c))))))
           :hints (("goal" :use ((:instance stack$c-top-minor-ordered-necc
                                  (i (nfix n)) (j (+ -1 (stack$c-top-frame stack$c)))
                                  (limit (stack$c-top-frame stack$c))))))))

  (defret stack$c-okp-of-<fn>
    (implies (and (stack$c-okp stack$c)
                  (< 1 (stack$c-frames stack$c))
                  (eql 1 (stack$c-minor-frames stack$c))
                  (eql (stack$c-scratch-len stack$c) 0))
             (stack$c-okp new-stack$c))
    :hints (("goal" :in-theory (e/d (stack$c-scratch-len stack$c-minor-frames stack$c-frames)))
            (and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (member (car lit) '(stack$c-major-frames-welltyped
                                            stack$c-minor-frames-welltyped
                                            stack$c-major-frames-bounded
                                            stack$c-minor-frames-bounded
                                            stack$c-top-minor-ordered
                                            stack$c-scratch-codeslots-ok
                                            stack$c-next-scratch-ordered
                                            stack$c-next-scratch-bounded
                                            stack$c-top-minor-bounded
                                            stack$c-scratch-welltyped))
                        `(:expand (,lit)))))))


  (local (defthm stack$c-minor-frames-equal-1
           (implies (and (equal (stack$c-minor-frames stack$c) 1)
                         (< 0 (stack$c-top-frame stack$c))
                         (equal k (+ -1 (nth-nat *stack$c-top-frame1* stack$c))))
                    (equal (nth-nat k
                                    (nth *stack$c-frame-top-minori1* stack$c))
                           (+ -1 (stack$c-top-minor stack$c))))
           :hints(("Goal" :in-theory (enable stack$c-minor-frames)))))

  (defret stack$c-extract-of-<fn>
    (implies (and (stack$c-okp stack$c)
                  (< 1 (stack$c-frames stack$c))
                  (eql 1 (stack$c-minor-frames stack$c))
                  (eql (stack$c-scratch-len stack$c) 0))
             (equal (stack$c-extract new-stack$c)
                    (stack$a-pop-frame (stack$c-extract stack$c))))
    :hints (("goal" :in-theory (e/d (stack$c-extract
                                     stack$c-build-top-major-frame
                                     stack$c-build-major-frame
                                     stack$a-pop-frame
                                     stack$c-scratch-len
                                     stack$c-frames
                                     stack$c-minor-frames)
                                    (scratch-incr-nontagidx-in-terms-of-conversions
                                     scratch-decr-nontagidx-in-terms-of-conversions))
             :expand ((stack$c-build-major-frames (+ -1 (nth-nat *stack$c-top-frame1* stack$c)) stack$c)
                      (:free (n) (stack$c-build-minor-frames n n stack$c))
                      (:free (n)
                       (stack$c-build-minor-frames
                        n (+ -1 (nth-nat *stack$c-top-minor1* stack$c))
                        stack$c)))))))





(defsection create-stack$c
  (local (defthm nth-open-cons
           (equal (nth n (cons a b))
                  (if (zp n)
                      a
                    (nth (1- n) b)))
           :hints(("Goal" :in-theory (enable nth)))))

  (defthm stack$c-okp-of-create-stack$c
    (stack$c-okp (create-stack$c))
    :hints(("Goal" :in-theory (enable stack$c-major-frames-welltyped
                                      stack$c-minor-frames-welltyped
                                      stack$c-major-frames-bounded
                                      stack$c-minor-frames-bounded
                                      stack$c-top-minor-ordered
                                      stack$c-scratch-codeslots-ok
                                      stack$c-next-scratch-ordered
                                      stack$c-next-scratch-bounded
                                      stack$c-top-minor-bounded
                                      stack$c-scratch-welltyped
                                      acl2::nth-when-too-large-cheap
                                      nth nth-scratch))))

  (defthm stack$c-extract-of-create-stack$c
    (equal (Stack$c-extract (create-stack$c))
           (create-stack$a))
    :hints(("Goal" :in-theory (enable stack$c-extract
                                      stack$c-build-top-major-frame
                                      stack$c-build-minor-frame)))))

(define stack$c-empty (stack$c)
  :guard-hints (("goal" :in-theory (enable update-nth nth len update-nth-array resize-list)
                 :do-not-induct t))
  :prepwork ((local (defthm equal-of-len
                      (implies (syntaxp (quotep n))
                               (equal (equal (len x) n)
                                      (if (zp n)
                                          (and (equal n 0)
                                               (not (consp x)))
                                        (and (consp x)
                                             (equal (len (cdr x)) (1- n))))))
                      :hints(("Goal" :in-theory (enable len)))))
             (local (defund resize-list-elem (x default)
                      (if (consp x) (car x) default)))
             (local (defthm resize-list-of-const
                      (implies (syntaxp (Quotep n))
                               (equal (resize-list x n default)
                                      (if (zp n)
                                          nil
                                        (cons (resize-list-elem x default)
                                              (resize-list (cdr x) (1- n) default)))))
                      :hints(("Goal" :in-theory (enable resize-list resize-list-elem))))))
  :enabled t
  (mbe :logic (non-exec (create-stack$c))
       :exec
       (b* ((stack$c (resize-stack$c-minor 3 stack$c))
            (stack$c (update-stack$c-minori 0 nil stack$c))
            (stack$c (update-stack$c-minori 1 nil stack$c))
            (stack$c (update-stack$c-minori 2 nil stack$c))
            (stack$c (resize-stack$c-major 3 stack$c))
            (stack$c (update-stack$c-majori 0 nil stack$c))
            (stack$c (update-stack$c-majori 1 nil stack$c))
            (stack$c (update-stack$c-majori 2 nil stack$c))
            (stack$c (resize-stack$c-scratch 2 stack$c))
            (stack$c (update-stack$c-scratchi1 0 0 stack$c))
            (stack$c (update-stack$c-scratchi1 1 0 stack$c))
            (stack$c (resize-stack$c-frame-top-minor 0 stack$c))
            (stack$c (resize-stack$c-frame-next-scratch 0 stack$c))
            (stack$c (update-stack$c-top-frame1 0 stack$c))
            (stack$c (update-stack$c-top-minor1 0 stack$c)))
         (update-stack$c-next-scratch1 1 stack$c))))
            








    
       





(local
 (progn
   (define stack-corr (stack$c stack$a)
     :non-executable t
     :enabled t
     :verify-guards nil
     (and (stack$c-okp stack$c)
          (equal (stack$c-extract stack$c) stack$a)))
))

(local (in-theory (disable stack$c-okp create-stack$c (create-stack$c))))


;; (local
;;  (make-event
;;   `(in-theory (disable . ,(acl2::template-append
;;                            '(stack$a-top-scratch-<kind>
;;                              stack$a-nth-scratch-<kind>
;;                              stack$a-push-scratch-<kind>)
;;                            *scratchobj-tmplsubsts*)))))

(make-event
 `(defabsstobj-events stack
    :concrete stack$c
    :corr-fn stack-corr
    :recognizer (stackp :logic major-stack-p
                        :exec stack$cp)
    :creator (create-stack :logic create-stack$a
                           :exec create-stack$c)
    :exports ((stack-frames :logic stack$a-frames :exec stack$c-frames)
              (stack-push-frame :logic stack$a-push-frame :exec stack$c-push-frame :protect t)
              (stack-minor-frames :logic stack$a-minor-frames :exec stack$c-minor-frames)
              (stack-nth-frame-minor-frames :logic stack$a-nth-frame-minor-frames :exec stack$c-nth-frame-minor-frames)
              (stack-push-minor-frame :logic stack$a-push-minor-frame :exec stack$c-push-minor-frame :protect t)
              (stack-set-bindings :logic stack$a-set-bindings :exec stack$c-set-bindings)
              (stack-add-binding :logic stack$a-add-binding :exec stack$c-add-binding)
              (stack-set-rule :logic stack$a-set-rule :exec stack$c-set-rule)
              (stack-set-phase :logic stack$a-set-phase :exec stack$c-set-phase)
              (stack-set-term :logic stack$a-set-term :exec stack$c-set-term)
              (stack-set-term-index :logic stack$a-set-term-index :exec stack$c-set-term-index)
              (stack-set-minor-bindings :logic stack$a-set-minor-bindings :exec stack$c-set-minor-bindings)
              (stack-add-minor-bindings :logic stack$a-add-minor-bindings :exec stack$c-add-minor-bindings)
              (stack-bindings :logic stack$a-bindings :exec stack$c-bindings)
              (stack-nth-frame-bindings :logic stack$a-nth-frame-bindings :exec stack$c-nth-frame-bindings)
              (stack-minor-bindings :logic stack$a-minor-bindings :exec stack$c-minor-bindings)
              (stack-nth-frame-minor-bindings :logic stack$a-nth-frame-minor-bindings :exec stack$c-nth-frame-minor-bindings)
              (stack-rule :logic stack$a-rule :exec stack$c-rule)
              (stack-phase :logic stack$a-phase :exec stack$c-phase)
              (stack-term :logic stack$a-term :exec stack$c-term)
              (stack-term-index :logic stack$a-term-index :exec stack$c-term-index)
              (stack-scratch-len :logic stack$a-scratch-len :exec stack$c-scratch-len)
              (stack-full-scratch-len :logic stack$a-full-scratch-len :exec stack$c-full-scratch-len)
              (stack-push-scratch :logic stack$a-push-scratch :exec stack$c-push-scratch :protect t)
              (stack-top-scratch :logic stack$a-top-scratch :exec stack$c-top-scratch)
              (stack-nth-scratch :logic stack$a-nth-scratch :exec stack$c-nth-scratch)
              (stack-nth-scratch-kind :logic stack$a-nth-scratch-kind :exec stack$c-nth-scratch-kind)
              (stack-update-scratch :logic stack$a-update-scratch :exec stack$c-update-scratch :protect t)
              (stack-pop-scratch :logic stack$a-pop-scratch :exec stack$c-pop-scratch :protect t)
              ,@(acl2::template-append
                 '((stack-push-scratch-<kind> :logic stack$a-push-scratch-<kind> :exec stack$c-push-scratch-<kind> :protect t)
                   (stack-top-scratch-<kind> :logic stack$a-top-scratch-<kind> :exec stack$c-top-scratch-<kind>)
                   (stack-nth-scratch-<kind> :logic stack$a-nth-scratch-<kind> :exec stack$c-nth-scratch-<kind>)
                   (stack-update-scratch-<kind> :logic stack$a-update-scratch-<kind> :exec stack$c-update-scratch-<kind> :protect t)
                   (stack-pop-scratch-<kind> :logic stack$a-pop-scratch-<kind> :exec stack$c-pop-scratch-<kind> :protect t))
                 *scratchobj-tmplsubsts*)
              (stack-pop-minor-frame :logic stack$a-pop-minor-frame :exec stack$c-pop-minor-frame :protect t)
              (stack-pop-frame :logic stack$a-pop-frame :exec stack$c-pop-frame :protect t)
              (stack-extract :logic stack$a-extract :exec stack$c-extract)
              (stack-empty :logic stack$a-empty :exec stack$c-empty :protect t))))
