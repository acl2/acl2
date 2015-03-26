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

(in-package "GL")
(include-book "def-gl-rewrite")
(include-book "symbolic-arithmetic")
(local (include-book "centaur/bitops/congruences" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(def-gl-rewrite integerp-of-logapp
  (integerp (logapp a b c)))

(defun plus-of-logapp-ind (n a c carry)
  (if (zp n)
      (list a c carry)
    (plus-of-logapp-ind (1- n) (logcdr a) (logcdr c)
                        (b-ior (b-and carry (logcar a))
                               (b-and carry (logcar c))))))

(local
 (defthmd plus-of-logapp-lemma
   (implies (and (bitp carry) (integerp c))
            (equal (+ (logapp n a b) c carry)
                   (+ (+ carry
                         (loghead n a)
                         (loghead n c))
                      (ash (+ (ifix b) (logtail n c)) (nfix n)))))
   :hints(("Goal" :in-theory (enable* acl2::ihsext-recursive-redefs)
           :induct (plus-of-logapp-ind n a c carry))
          (and stable-under-simplificationp
               '(:in-theory (enable bitops::equal-logcons-strong
                                    b-xor b-and b-ior))))))

(def-gl-rewrite plus-of-logapp-1
  (implies (integerp c)
           (equal (+ (logapp n a b) c)
                  (+ (+ (loghead n a)
                        (loghead n c))
                     (ash (+ (ifix b) (logtail n c)) (nfix n)))))
  :hints (("goal" :use ((:instance plus-of-logapp-lemma
                         (carry 0)))
           :in-theory (disable plus-of-logapp-lemma))))

(def-gl-rewrite plus-of-logapp-2
  (implies (integerp c)
           (equal (+ c (logapp n a b))
                  (+ (+ (loghead n a)
                        (loghead n c))
                     (ash (+ (ifix b) (logtail n c)) (nfix n)))))
  :hints (("goal" :use ((:instance plus-of-logapp-lemma
                         (carry 0)))
           :in-theory (disable plus-of-logapp-lemma))))

;; (def-gl-rewrite loghead-of-logapp
;;   (implies (<= (nfix n) (nfix m))
;;            (equal (loghead n (logapp m a b))
;;                   (loghead n a)))
;;   :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
;;                                      acl2::ihsext-recursive-redefs))))

(def-gl-rewrite loghead-of-logapp
  (equal (loghead n (logapp m a b))
         (logapp (min (nfix m) (nfix n)) a (loghead (nfix (- (nfix n) (nfix m))) b)))
  :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                     acl2::ihsext-recursive-redefs))))

(def-gl-rewrite loghead-of-0
  (equal (loghead 0 x) 0))

(defun term-gobj-p (x)
  (and (consp x)
       (member (car x) '(:g-apply :g-var :g-ite))))

(def-gl-rewrite logapp-tail-0
  (implies (syntaxp (and (integerp n)
                         (term-gobj-p a)))
           (equal (logapp n a 0) (loghead n a))))

(def-gl-rewrite logbitp-of-logapp
  (equal (logbitp n (logapp m a b))
         (if (< (nfix n) (nfix m))
             (logbitp n a)
           (logbitp (- (nfix n) (nfix m)) b)))
  :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                     acl2::ihsext-recursive-redefs))))

(def-gl-rewrite loghead-of-plus
  (implies (and (integerp a) (integerp b))
           (equal (loghead n (+ a b))
                  (loghead n (+ (loghead n a) (loghead n b)))))
  :hints(("Goal" :use ((:instance bitops::loghead-of-plus-loghead-first
                        (m n))
                       (:instance bitops::loghead-of-plus-loghead-first
                        (m n) (a (loghead n b)) (b a))))))

(def-gl-rewrite logbitp-of-plus
  (implies (and (integerp a) (integerp b))
           (equal (logbitp n (+ a b))
                  (logbitp n (+ (loghead (+ 1 (nfix n)) a)
                                (loghead (+ 1 (nfix n)) b)))))
  :hints (("goal" :in-theory (e/d* (acl2::bitops-congruences)
                                   (bitops::bitops-congruence-incompatible)))))


(def-gl-rewrite logand-of-logapp
  (equal (logand mask (logapp n a b))
         (logapp n (logand mask a)
                 (logand (logtail n mask) b)))
  :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                     acl2::ihsext-recursive-redefs))))

(def-gl-rewrite logand-of-logapp-2
  (equal (logand (logapp n a b) mask)
         (logapp n (logand mask a)
                 (logand (logtail n mask) b)))
  :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                     acl2::ihsext-recursive-redefs))))

(def-gl-rewrite logior-of-logapp
  (equal (logior mask (logapp n a b))
         (logapp n (logior mask a)
                 (logior (logtail n mask) b)))
  :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                     acl2::ihsext-recursive-redefs))))

(def-gl-rewrite logior-of-logapp-2
  (equal (logior (logapp n a b) mask)
         (logapp n (logior mask a)
                 (logior (logtail n mask) b)))
  :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                     acl2::ihsext-recursive-redefs))))

(def-gl-rewrite logtail-of-logapp
  (equal (logtail m (logapp n a b))
         (logapp (- (nfix n) (nfix m))
                 (logtail m a)
                 (logtail (- (nfix m) (nfix n)) b)))
  :hints(("Goal" :in-theory (e/d* (acl2::ihsext-inductions
                                     acl2::ihsext-recursive-redefs)
                                  (acl2::logtail-identity
                                   acl2::bitmaskp**)))))

(def-gl-rewrite logand-minus-1-first
  (equal (logand -1 n)
         (ifix n)))

(def-gl-rewrite logand-minus-1-second
  (equal (logand n -1)
         (ifix n)))

(def-gl-rewrite logior-minus-1-first
  (equal (logior -1 n) -1))

(def-gl-rewrite logior-minus-1-second
  (equal (logior n -1) -1))

(def-gl-rewrite logior-0-first
  (equal (logior 0 n) (ifix n)))

(def-gl-rewrite logior-0-second
  (equal (logior 0 n) (ifix n)))

(def-gl-rewrite ifix-of-logapp
  (equal (ifix (logapp n a b))
         (logapp n a b)))

;; (def-gl-rewrite logand-of-logapp
;;   (implies (and (<= 0 (ifix mask))
;;                 (< (ifix mask) (ash 1 (nfix n))))
;;            (equal (logand mask (logapp n a b))
;;                   (logand mask a)))
;;   :hints (("goal" :in-theory (enable* acl2::ihsext-recursive-redefs
;;                                      acl2::ihsext-inductions))))

(def-gl-rewrite integerp-of-maybe-integer
  (equal (integerp (maybe-integer i x intp))
         (and intp t))
  :hints(("Goal" :in-theory (enable maybe-integer))))

(def-gl-rewrite <-of-maybe-integer-1
  (implies intp
           (equal (< (maybe-integer i x intp) a)
                  (< (ifix i) a)))
  :hints(("Goal" :in-theory (enable maybe-integer))))

(def-gl-rewrite <-of-maybe-integer-2
  (implies intp
           (equal (< a (maybe-integer i x intp))
                  (< a (ifix i))))
  :hints(("Goal" :in-theory (enable maybe-integer))))

(local (defthm <-logapp-0-local
         (equal (< (logapp n i j) 0)
                (< (ifix j) 0))
         :hints(("Goal" :in-theory (e/d* ;; acl2::ihsext-bounds-thms
                                    (acl2::ihsext-recursive-redefs
                                     acl2::ihsext-inductions)
                                    ((force)))))))
(def-gl-rewrite <-logapp-0
  (equal (< (logapp n i j) 0)
         (< (ifix j) 0)))

(def-gl-rewrite integerp-int-set-sign
  (integerp (int-set-sign negp i)))

(def-gl-rewrite <-int-set-sign-0
  (equal (< (int-set-sign negp i) 0)
         (and negp t)))

(defun ifix-or-zero (ip i)
  (if ip (ifix i) 0))

(def-gl-rewrite ifix-of-maybe-integer
  (equal (ifix (maybe-integer i x intp))
         (ifix-or-zero intp i))
  :hints(("Goal" :in-theory (enable maybe-integer))))

(def-gl-rewrite ifix-or-zero-of-logapp
  (equal (ifix-or-zero ip (logapp n a b))
         (logapp n (ifix-or-zero ip a)
                 (ifix-or-zero ip b))))

(def-gl-rewrite ifix-or-zero-of-int-set-sign
  (equal (ifix-or-zero ip (int-set-sign negp i))
         (int-set-sign (and ip negp) (ifix-or-zero ip i)))
  :hints(("Goal" :in-theory (enable int-set-sign))))

(defun nfix-or-zero (ip i)
  (if ip (nfix i) 0))

(def-gl-rewrite nfix-of-maybe-integer
  (equal (nfix (maybe-integer i x intp))
         (nfix-or-zero intp i))
  :hints(("Goal" :in-theory (enable maybe-integer))))

(local (defthm logapp-with-non-integer
         (implies (zip b)
                  (equal (logapp n a b)
                         (loghead n a)))))

(def-gl-rewrite nfix-or-zero-of-logapp
  (equal (nfix-or-zero ip (logapp n a b))
         (logapp n (ifix-or-zero (and ip (<= 0 (ifix b))) a)
                 (nfix-or-zero ip b)))
  :hints(("Goal" :in-theory (enable nfix))))

(local (defthm loghead-with-zip
         (implies (zip a)
                  (equal (loghead n a) 0))))

(def-gl-rewrite loghead-of-maybe-integer
  (equal (loghead n (maybe-integer i x intp))
         (ifix-or-zero intp (loghead n (ifix i))))
  :hints(("Goal" :in-theory (enable non-int-fix maybe-integer))))

(def-gl-rewrite ifix-or-zero-of-loghead
  (equal (ifix-or-zero ip (loghead n i))
         (loghead n (ifix-or-zero ip i))))


(def-gl-rewrite equal-of-logapp
  (equal (equal (logapp n a b) c)
         (and (integerp c)
              (equal (loghead n c) (loghead n a))
              (equal (logtail n c) (ifix b))))
  :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                     acl2::ihsext-recursive-redefs))))

(def-gl-rewrite logand-0-first
  (equal (logand 0 x)
         0))

(def-gl-rewrite logand-0-second
  (equal (logand x 0)
         0))

(def-gl-rewrite integerp-floor
  (equal (integerp (floor x y)) t))

;; (local (defthm logapp-of-non-integer-second
;;          (implies (not (integerp b))
;;                   (equal (logapp n a b)
;;                          (logapp n a 0)))
;;          :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
;;                                             acl2::ihsext-recursive-redefs)))
;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

#||




(trace$ gl::glcp-unify-term/gobj)

(thm (IMPLIES
      (and (GL::INTEGER-WITH-NBITSP 64 ACL2::X0)
           (UNSIGNED-BYTE-P 64 ACL2::X1)
           (UNSIGNED-BYTE-P 64 ACL2::X2))
      (OR (LOGBITP 10 ACL2::X1)
          (EQUAL (UNSIGNED-BYTE-FIX 64
                                    (AAA_AAS-G7 ACL2::X2 (LOGHEAD 64 ACL2::X0)))
                 (LOGIOR 2 (ACL2::LOGSQUASH 32 ACL2::X2)
                         (LOGAND 2261 ACL2::X0)))))
     :hints (("goal" :in-theory nil)
             (gl::try-gl
              ;; :fixes
              ;; (((nfix (st-get :eflags st)) (loghead 64 acl2::x)))
              :subterms-types
              (((nfix (st-get :eflags st))              (gl::integer-with-nbitsp 64 acl2::x))
               ((u64-tr-get n g)                        (unsigned-byte-p 64 acl2::x))
;            ((st-set :pc val st)                     (unknownp acl2::x))
               ((st-get :oracle st)                     (unknownp acl2::x)))
              :type-gens (((unknownp acl2::x) (gl::g-var 0)))
;           :bad-subterms (st)
              )))

||#

(gl::def-gl-rewrite not-to-if
  (iff (not x)
       (if x nil t)))


;; (defthm merge-if-of-cons
;;   (implies (consp z)
;;            (equal (if c (cons x y) z)
;;                   (cons (if c x (car z))
;;                         (if c y (cdr z)))))
;;   :rule-classes nil)

;; (table gl-branch-merge-rules
;;        'cons
;;        '(merge-if-of-cons))
