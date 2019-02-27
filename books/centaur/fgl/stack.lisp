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

(local (fty::deflist gl-objectlist :elt-type gl-object :true-listp t))

(local (in-theory (disable nth acl2::nth-when-zp update-nth)))

;; A stack is (logically) just a list of stack-frames, where each frame has a
;; binding list BINDINGS, an objectlist SCRATCH, and a debug field (type yet
;; undetermined).  The topmost stack frame is the first one.


(fty::defprod stack-frame
  ((bindings gl-object-alist-p)
   (scratch gl-objectlist-p)
   (debug)))

(fty::deflist stack$a :elt-type stack-frame :true-listp t :non-emptyp t
  ///
  (defthm stack$a-p-of-cons-cdr
    (implies (and (stack$a-p x)
                  (stack-frame-p a))
             (stack$a-p (cons a (cdr x))))
    :hints(("Goal" :in-theory (enable stack$a-p)))))

(define stack$a-push-frame ((x stack$a-p))
  :enabled t
  (cons (make-stack-frame) (stack$a-fix x)))

(define stack$a-len ((x stack$a-p))
  :enabled t
  (len x))


(local (defthm gl-object-alist-p-of-append
           (implies (and (gl-object-alist-p x)
                         (gl-object-alist-p y))
                    (gl-object-alist-p (append x y)))))

(define stack$a-set-bindings ((bindings gl-object-alist-p)
                              (x stack$a-p))
  :enabled t
  (stack$a-fix (cons (change-stack-frame (car x) :bindings bindings)
                     (cdr x))))

(define stack$a-add-bindings ((bindings gl-object-alist-p)
                              (x stack$a-p))
  :enabled t
  (b* (((stack-frame frame) (car x)))
    (stack$a-fix (cons (change-stack-frame frame :bindings (append bindings frame.bindings))
                       (cdr x)))))

(define stack$a-push-scratch ((obj gl-object-p)
                              (x stack$a-p))
  :enabled t
  (b* (((stack-frame frame) (car x)))
    (stack$a-fix (cons (change-stack-frame frame :scratch (cons obj frame.scratch))
                       (cdr x)))))

(define stack$a-set-debug ((debug)
                           (x stack$a-p))
  :enabled t
  (b* ((frame (car x)))
    (stack$a-fix (cons (change-stack-frame frame :debug debug)
                       (cdr x)))))

(define stack$a-bindings ((x stack$a-p))
  :enabled t
  (stack-frame->bindings (car x)))

(define stack$a-scratchlen ((x stack$a-p))
  :enabled t
  (len (stack-frame->scratch (car x))))


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

(define stack$a-peek-scratch ((n natp)
                              (x stack$a-p))
  :guard (<= n (stack$a-scratchlen x))
  :enabled t
  (b* (((stack-frame frame) (car x)))
    (rev-take n frame.scratch)))


(define stack$a-pop-scratch ((n natp)
                             (x stack$a-p))
  :guard (<= n (stack$a-scratchlen x))
  :enabled t
  (b* (((stack-frame frame) (car x)))
    (stack$a-fix (cons (change-stack-frame frame :scratch (nthcdr n frame.scratch))
                       (cdr x)))))

(local
 (defthm stack-frame-p-of-nth-when-stack$a-p
   (implies (and (stack$a-p x)
                 (< (nfix n) (len x)))
            (stack-frame-p (nth n x)))
   :hints(("Goal" :in-theory (enable stack$a-p nth)))))

(define stack$a-nth-frame ((n natp)
                           (x stack$a-p))
  ;; for debugging mostly
  :enabled t
  :guard (< n (stack$a-len x))
  (stack-frame-fix (nth n x)))

(defthm stack$a-p-of-cdr
  (implies (and (stack$a-p x)
                (< 1 (len x)))
           (stack$a-p (cdr x)))
  :hints(("Goal" :in-theory (enable stack$a-p))))
                  
       
(define stack$a-pop-frame ((x stack$a-p))
  :enabled t
  :guard (< 1 (stack$a-len x))
  (stack$a-fix (cdr x)))

(define create-stack$a ()
  :enabled t
  (list (make-stack-frame)))



(defstobj stack$c
  (stack$c-array :type (array t (3)) :resizable t)
  (stack$c-nframes :type (integer 1 *) :initially 1))


(defun-sk stack$c-welltyped (stack$c)
  (forall i
          (implies (natp i)
                   (and (gl-object-alist-p (nth (* 3 i) (nth *stack$c-arrayi* stack$c)))
                        (gl-objectlist-p (nth (+ 1 (* 3 i)) (nth *stack$c-arrayi* stack$c))))))
  :rewrite :direct)

(in-theory (disable stack$c-welltyped))

(defthm stack$c-welltyped-implies-gl-object-alist-p
  (implies (and (stack$c-welltyped stack$c)
                (posp n) (<= n (stack$c-nframes stack$c)))
           (gl-object-alist-p (nth (+ -3 (* 3 n)) (nth *stack$c-arrayi* stack$c))))
  :hints (("goal" :use ((:instance stack$c-welltyped-necc (i (1- n))))
           :in-theory (disable stack$c-welltyped-necc))))

(defthm stack$c-welltyped-implies-gl-objectlist-p
  (implies (and (stack$c-welltyped stack$c)
                (posp n) (<= n (stack$c-nframes stack$c)))
           (gl-objectlist-p (nth (+ -2 (* 3 n)) (nth *stack$c-arrayi* stack$c))))
  :hints (("goal" :use ((:instance stack$c-welltyped-necc (i (1- n))))
           :in-theory (disable stack$c-welltyped-necc))))

(defun-sk stack$c-bounded (stack$c)
  ;; Elements outside the frames are all set to 0.
  (forall i
          (implies (and (natp i)
                        (<= (* 3 (stack$c-nframes stack$c)) i))
                   (equal (nth i (nth *stack$c-arrayi* stack$c)) nil)))
  :rewrite :direct)

(in-theory (disable stack$c-bounded))

(define stack$c-okp (stack$c)
  :enabled t
  (and (<= (* 3 (stack$c-nframes stack$c)) (stack$c-array-length stack$c))
       (ec-call (stack$c-welltyped stack$c))
       (ec-call (stack$c-bounded stack$c))))



(define stack$c-push-frame ((stack$c stack$c-okp))
  :enabled t
  (b* ((new-len (* 3 (+ 1 (stack$c-nframes stack$c))))
       (stack$c (if (< (stack$c-array-length stack$c) new-len)
                    (resize-stack$c-array (max 30 (* 2 new-len)) stack$c)
                  stack$c)))
    (update-stack$c-nframes (+ 1 (stack$c-nframes stack$c)) stack$c)))


(define stack$c-len (stack$c)
  :enabled t
  (stack$c-nframes stack$c))

(define stack$c-set-bindings ((bindings gl-object-alist-p)
                              (stack$c stack$c-okp))
  :enabled t
  (update-stack$c-arrayi (- (* 3 (stack$c-nframes stack$c)) 3) bindings stack$c))

(define stack$c-add-bindings ((bindings gl-object-alist-p)
                              (stack$c stack$c-okp))
  :enabled t
  (b* ((index (- (* 3 (stack$c-nframes stack$c)) 3))
       (curr-bindings (stack$c-arrayi index stack$c)))
    (update-stack$c-arrayi index (append bindings curr-bindings) stack$c)))

(define stack$c-push-scratch ((obj gl-object-p)
                              (stack$c stack$c-okp))
  :enabled t
  (b* ((index (- (* 3 (stack$c-nframes stack$c)) 2))
       (curr-scratch (stack$c-arrayi index stack$c)))
    (update-stack$c-arrayi index (cons obj curr-scratch) stack$c)))

(define stack$c-set-debug ((obj)
                           (stack$c stack$c-okp))
  :enabled t
  (b* ((index (- (* 3 (stack$c-nframes stack$c)) 1)))
    (update-stack$c-arrayi index obj stack$c)))

(define stack$c-bindings ((stack$c stack$c-okp))
  :enabled t
  (stack$c-arrayi (- (* 3 (stack$c-nframes stack$c)) 3) stack$c))

(define stack$c-scratchlen ((stack$c stack$c-okp))
  :enabled t
  (len (stack$c-arrayi (- (* 3 (stack$c-nframes stack$c)) 2) stack$c)))

(local (defthm true-listp-when-gl-objectlist-p-rw
         (implies (gl-objectlist-p x)
                  (true-listp x))))

(define stack$c-peek-scratch ((n natp)
                              (stack$c stack$c-okp))
  :guard (<= n (stack$c-scratchlen stack$c))
  :enabled t
  (rev-take n (stack$c-arrayi (- (* 3 (stack$c-nframes stack$c)) 2) stack$c)))

(define stack$c-pop-scratch ((n natp)
                             (stack$c stack$c-okp))
  :guard (<= n (stack$c-scratchlen stack$c))
  :enabled t
  (b* ((index (- (* 3 (stack$c-nframes stack$c)) 2)))
    (update-stack$c-arrayi index (nthcdr n (stack$c-arrayi index stack$c)) stack$c)))


;; (local
;;  (encapsulate nil
;;    (local (defthm negative-norm
;;             (equal (- x) (* -1 x))))
;;    (defthm const-times-negative
;;      (implies (syntaxp (quotep c))
;;               (equal (* c (- x))
;;                      (* (- c) x)))
;;      :hints (("goal" :use ((:instance associativity-of-*
;;                             (x -1) (y c) (z x))
;;                            (:instance associativity-of-*
;;                             (x c) (y -1) (z x)))
;;               :in-theory (disable associativity-of-*))))))



(define stack$c-nth-frame ((n natp)
                           (stack$c stack$c-okp))
  :enabled t
  :guard (< n (stack$c-len stack$c))
  :guard-hints (("goal" :in-theory (disable distributivity))
                (and stable-under-simplificationp
                     '(:in-theory (enable distributivity))))
  :prepwork ((local
              (encapsulate nil
                (defthm <-when-<=
                  (implies (and (<= a b)
                                (< c 0)
                                (<= d 0))
                           (< (+ c d a) b)))

                (local (defthmd foo1
                         (implies (and (integerp i)
                                       (< i 0)
                                       (<= -3 i)
                                       (posp m))
                                  (<= 0 (+ i (* 3 m))))))

                (defthm foo
                  (implies (and (integerp i)
                                (< i 0)
                                (<= -3 i)
                                (integerp n)
                                (natp m)
                                (< n m))
                           (<= 0 (+ i (* 3 (- n)) (* 3 m))))
                  :hints (("goal" :use ((:instance foo1 (m (- m n))))))))))
  (b* ((offset (* 3 (- (stack$c-len stack$c) n))))
    (make-stack-frame :bindings (stack$c-arrayi (- offset 3) stack$c)
                      :scratch (stack$c-arrayi (- offset 2) stack$c)
                      :debug (stack$c-arrayi (- offset 1) stack$c))))

(define stack$c-pop-frame ((stack$c stack$c-okp))
  :guard (< 1 (stack$c-len stack$c))
  :enabled t
  (b* ((offset (* 3 (stack$c-nframes stack$c)))
       (stack$c (update-stack$c-arrayi (- offset 1) nil stack$c))
       (stack$c (update-stack$c-arrayi (- offset 2) nil stack$c))
       (stack$c (update-stack$c-arrayi (- offset 3) nil stack$c)))
    (update-stack$c-nframes (1- (stack$c-nframes stack$c)) stack$c)))

(encapsulate nil
  (local (defun-sk stack-frames-corr (stack$c stack$a)
           (forall n
                   (implies (and (natp n)
                                 (< n (len stack$a)))
                            (and (equal (nth (* 3 n) (nth *stack$c-arrayi* stack$c))
                                        (stack-frame->bindings (nth (- (+ -1 (len stack$a)) n) stack$a)))
                                 (equal (nth (+ 1 (* 3 n)) (nth *stack$c-arrayi* stack$c))
                                        (stack-frame->scratch (nth (- (+ -1 (len stack$a)) n) stack$a)))
                                 (equal (nth (+ 2 (* 3 n)) (nth *stack$c-arrayi* stack$c))
                                        (stack-frame->debug (nth (- (+ -1 (len stack$a)) n) stack$a))))))
           :rewrite :direct))
  (local (in-theory (disable stack-frames-corr)))

  (local (defthm stack-frames-corr-offset
           (implies (and (stack-frames-corr stack$c stack$a)
                         (posp n)
                         (<= n (len stack$a)))
                    (and (equal (nth (+ -3 (* 3 n)) (nth *stack$c-arrayi* stack$c))
                                (stack-frame->bindings (nth (- (len stack$a) n) stack$a)))
                         (equal (nth (+ -2 (* 3 n)) (nth *stack$c-arrayi* stack$c))
                                (stack-frame->scratch (nth (- (len stack$a) n) stack$a)))
                         (equal (nth (+ -1 (* 3 n)) (nth *stack$c-arrayi* stack$c))
                                (stack-frame->debug (nth (- (len stack$a) n) stack$a)))))
           :hints (("goal" :use ((:instance stack-frames-corr-necc (n (1- n))))
                    :in-theory (disable stack-frames-corr-necc)))))

  (local (defthm stack-frames-corr-offset2
           (implies (and (stack-frames-corr stack$c stack$a)
                         (integerp m) (integerp n)
                         (posp (+ n m))
                         (<= (+ n m) (len stack$a)))
                    (and (equal (nth (+ -3 (* 3 n) (* 3 m)) (nth *stack$c-arrayi* stack$c))
                                (stack-frame->bindings (nth (- (len stack$a) (+ n m)) stack$a)))
                         (equal (nth (+ -2 (* 3 n) (* 3 m)) (nth *stack$c-arrayi* stack$c))
                                (stack-frame->scratch (nth (- (len stack$a) (+ n m)) stack$a)))
                         (equal (nth (+ -1 (* 3 n) (* 3 m)) (nth *stack$c-arrayi* stack$c))
                                (stack-frame->debug (nth (- (len stack$a) (+ n m)) stack$a)))))
           :hints (("goal" :use ((:instance stack-frames-corr-necc (n (1- (+ n m)))))
                    :in-theory (disable stack-frames-corr-necc)))))

  (local (defthm stack-frames-corr-zero-offset
           (implies (and (stack-frames-corr stack$c stack$a)
                         (integerp m) (integerp n)
                         (posp (+ n m))
                         (<= (+ n m) (len stack$a)))
                    (and (equal (nth 0 (nth *stack$c-arrayi* stack$c))
                                (stack-frame->bindings (nth (- (len stack$a) 1) stack$a)))
                         (equal (nth 1 (nth *stack$c-arrayi* stack$c))
                                (stack-frame->scratch (nth (- (len stack$a) 1) stack$a)))
                         (equal (nth 2 (nth *stack$c-arrayi* stack$c))
                                (stack-frame->debug (nth (- (len stack$a) 1) stack$a)))))
           :hints (("goal" :use ((:instance stack-frames-corr-necc (n 0)))
                    :in-theory (disable stack-frames-corr-necc)))))

  (local (define stack-corr (stack$c stack$a)
           :non-executable t
           :enabled t
           (and (stack$c-okp stack$c)
                (equal (stack$c-nframes stack$c) (len stack$a))
                (ec-call (stack-frames-corr stack$c stack$a)))))

  ;; (local (defthm nth-of-cons-when-zp
  ;;          (implies (zp n)
  ;;                   (equal (nth n (cons a b))
  ;;                          a))
  ;;          :hints(("Goal" :in-theory (enable nth)))))

  ;; (local (defthm nth-of-cons-when-posp
  ;;          (implies (posp n)
  ;;                   (equal (nth n (cons a b))
  ;;                          (nth (+ -1 n) b)))
  ;;          :hints(("Goal" :in-theory (enable nth)))))

  (local (defthm nth-of-cons-split
           (equal (nth n (cons a b))
                  (if (zp n)
                      a
                    (nth (+ -1 n) b)))
           :hints(("Goal" :in-theory (enable nth)))))

  

  (local (defthm equal-plus-consts
           (implies (syntaxp (and (quotep a) (quotep b)))
                    (equal (equal (+ a c) (+ b d))
                           (equal (+ (+ (- b) a) c) (fix d))))))

  (local (defthm equal-const-plus-3*
           (implies (syntaxp (quotep c))
                    (equal (equal (+ c (* 3 x)) (* 3 y))
                           (equal (+ (/ c 3) x) (fix y))))))

  
  (local (defthm len-cons
           (equal (len (cons a b))
                  (+ 1 (len b)))))

  (local (defthm nfix-when-natp
           (implies (natp n)
                    (equal (nfix n) n))))

  (local (defthm natp-when-integerp-gte-0
           (implies (and (integerp x)
                         (<= 0 x))
                    (natp x))))


  (local (defthm <=-max
           (implies (or (<= x a) (<= x b))
                    (<= x (max a b)))))

  (local (defthm <-max
           (implies (or (< x a) (< x b))
                    (< x (max a b)))))

  (local (defthm minus-minus
           (equal (- (- x)) (fix x))))

  (local (in-theory (disable len nfix not natp max
                             acl2::nth-when-atom
                             true-listp-update-nth
                             acl2::nth-when-too-large-cheap
                             resize-list nthcdr acl2::take-redefinition
                             append
                             acl2::nthcdr-when-zp)))

  (local (defthm len-when-stack$a-p
           (implies (stack$a-p x)
                    (posp (len x)))
           :hints(("Goal" :in-theory (enable stack$a-p)))
           :rule-classes :forward-chaining))


  (local (set-default-hints
          '((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   (and (or (eq (car lit) 'stack$c-welltyped)
                            (eq (car lit) 'stack$c-bounded)
                            (eq (car lit) 'stack-frames-corr))
                        `(:expand (,lit)))))
            ;; (and stable-under-simplificationp
            ;;      '(:in-theory (enable nth-of-cons-split)))
            )))
                             
  (defabsstobj-events stack
    :concrete stack$c
    :corr-fn stack-corr
    :recognizer (stackp :logic stack$a-p
                        :exec stack$cp)
    :creator (create-stack :logic create-stack$a
                           :exec create-stack$c)
    :exports ((stack-push-frame :logic stack$a-push-frame :exec stack$c-push-frame :protect t)
              (stack-len :logic stack$a-len :exec stack$c-len)
              (stack-set-bindings :logic stack$a-set-bindings :exec stack$c-set-bindings)
              (stack-add-bindings :logic stack$a-add-bindings :exec stack$c-add-bindings)
              (stack-push-scratch :logic stack$a-push-scratch :exec stack$c-push-scratch)
              (stack-set-debug :logic stack$a-set-debug :exec stack$c-set-debug)
              (stack-bindings :logic stack$a-bindings :exec stack$c-bindings)
              (stack-scratchlen :logic stack$a-scratchlen :exec stack$c-scratchlen)
              (stack-peek-scratch :logic stack$a-peek-scratch :exec stack$c-peek-scratch)
              (stack-pop-scratch :logic stack$a-pop-scratch :exec stack$c-pop-scratch)
              (stack-nth-frame :logic stack$a-nth-frame :exec stack$c-nth-frame)
              (stack-pop-frame :logic stack$a-pop-frame :exec stack$c-pop-frame :protect t)
              )))


       
