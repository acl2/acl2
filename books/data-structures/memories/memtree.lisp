;
; Memories: Array-like Records for ACL2
; Copyright (C) 2005-2006 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>
;



; memtree.lisp - implementation of memory trees
;
; This is an implementation file and should not be directly included in
; external work.  Use the interface file (memtree.lisp) instead!
;
; Memory trees are the real heart of our library, in that they are the
; structure which allows us to represent large memories and efficiently update
; them.

(in-package "MEM")
(set-verify-guards-eagerness 2)




; Preliminary arithmetic work
;
; We load Robert Krug's arithmetic-3 libraries, and then set up a few lemmas
; that will help us with guard verification and optimization.

(local (include-book "arithmetic-3/bind-free/top" :dir :system))
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(set-default-hints '((ACL2::nonlinearp-default-hint
                      ACL2::stable-under-simplificationp
                      ACL2::hist
                      ACL2::pspv)))

(local (defthm signed-byte-natural
         (implies (force (natp x))
                  (equal (signed-byte-p 29 x)
                         (< x (expt 2 28))))))

(local (defthm mask-to-mod
         (implies (force (natp n))
                  (equal (logand n 1)
                         (mod n 2)))))

(local (defthm ash-to-floor
         (implies (force (natp n))
                  (equal (ash n -1)
                         (floor n 2)))))

(local (in-theory (disable signed-byte-p)))
(local (in-theory (disable logand ash)))
(local (in-theory (disable (:executable-counterpart expt))))

; [Jared] dumb speed hacking
(local (in-theory (disable acl2::floor-bounds-1
                           acl2::floor-zero
                           acl2::mod-zero
                           acl2::mod-x-y-=-x
                           acl2::floor-positive
                           acl2::floor-negative
                           acl2::mod-positive
                           acl2::mod-negative
                           acl2::not-integerp-4a
                           acl2::not-integerp-2a
                           acl2::not-integerp-1a
                           acl2::mod-bounds-3
                           acl2::mod-nonpositive
                           acl2::floor-nonpositive-1
                           acl2::floor-nonpositive-2
                           acl2::floor-nonnegative-1
                           acl2::floor-nonnegative-2
                           default-*-2
                           default-*-1
                           default-<-2
                           default-<-1
                           acl2::mod-completion
                           acl2::mod-cancel-*
                           acl2::mod-neg
                           acl2::mod-minus-2
                           acl2::mod-bounds-2

                           )))




; Definition of memory trees.  Our memory trees are laid out so that they have
; some fixed depth, and the actual data is at the tips of the tree.  Naturally,
; each tree can hold 2^{depth} elements.  These are an internal structure not
; meant for outside use.
;
; We require that memory trees are "canonical" in the sense that they take as
; little space as possible.  More formally, in a memtree all nil values must be
; joined as closely as possible to the root of the tree.  For example, we would
; say that nil is a memtree, but (nil . nil) is not because it can be
; represented more concisely using just nil.  We provide an actual definition
; of this below.

(defun _memtree-p (mtree depth)
  (declare (xargs :guard (natp depth)))
  (if (zp depth)
      t
    (if (atom mtree)
        (null mtree)
      (and (_memtree-p (car mtree) (1- depth))
           (_memtree-p (cdr mtree) (1- depth))
           (not (and (null (car mtree))
                     (null (cdr mtree))))))))

(defun _memtree-fix (mtree depth)
  (declare (ignorable depth) ; added by Matt K. after 3.0.1 to suppress compiler warning
           (xargs :guard (and (natp depth)
                              (_memtree-p mtree depth))))
  (if (mbt (_memtree-p mtree depth))
      mtree
    nil))

(defthm _memtree-fix-memtree
  (_memtree-p (_memtree-fix mtree depth) depth))

(defthm _memtree-fix-identity
  (implies (_memtree-p mtree depth)
           (equal (_memtree-fix mtree depth) mtree)))

(defthm |(_memtree-fix mtree 0)|
  (equal (_memtree-fix mtree 0)
         mtree))

(defthm |(_memtree-p mtree 0)|
  (_memtree-p mtree 0))

(defthm |(_memtree-p nil depth)|
  (_memtree-p nil depth))




; Definition of memory tree addresses.  Valid addresses for a tree of some
; depth are then only the integers in the range [0, 2^{depth}).

(defun _address-p (addr depth)
  (declare (xargs :guard (natp depth)))
  (and (natp addr)
       (< addr (expt 2 (nfix depth)))))

(defun _address-fix (addr depth)
  (declare (ignorable depth) ; added by Matt K. after 3.0.1 to suppress compiler warning
           (xargs :guard (and (natp depth)
                              (_address-p addr depth))))
  (if (mbt (_address-p addr depth))
      addr
    0))

(defthm |(_address-p addr 0)|
  (implies (_address-p addr 0)
           (equal addr 0))
  :rule-classes :forward-chaining)

(defthm |(_address-p 0 depth)|
  (_address-p 0 depth))

(defthm _address-forward-to-natural
  (implies (_address-p addr depth)
           (and (integerp addr)
                (<= 0 addr)))
  :rule-classes :forward-chaining)

(defthm _address-upper-bound
  (implies (and (natp depth)
                (_address-p addr depth))
           (< addr (expt 2 depth)))
  :rule-classes :linear)

(defthm _address-fix-address
  (_address-p (_address-fix addr depth) depth))

(defthm _address-fix-identity
  (implies (_address-p addr depth)
           (equal (_address-fix addr depth) addr)))

(defthm _address-fix-natural
  (and (integerp (_address-fix addr depth))
       (<= 0 (_address-fix addr depth)))
  :rule-classes :type-prescription)

(in-theory (disable _address-fix _memtree-fix))




; Definition of memory tree loading operations.
;
; We consider there to be two ways for an address space to be laid out using
; binary trees.  In an "MSB" style tree, the most significant bit of the
; address is used at each step in order to get to determine which way to go.
; This has the advantage that memory is laid out in the "most natural" fashion
; -- i.e., 0 is the caaaaaaaaaaaa....aaaar of the tree, and the maximum element
; is the cdddddddd....dddddr of the tree.
;
; In the perhaps less natural "LSB" style, the least significant bit of the
; address is used at each step in order to determine which way to go.  This
; gives you a really strange memory, where e.g., all the odd addresses are on
; the right hand side and all the even addresses are on the left, and so forth
; down the tree.  However, the advantage is that load and store are very easy
; to write, because you can simply floor and mod the address by 2 at each step
; (or use the equivalent bit-test and shift operations) to find your address.
;
; One potential disadvantage of the LSB approach is that it is not possible to
; create "very efficient traversals" of the memory space.  But we really don't
; think this is a problem.  For example, we expect that a user would simply
; call "store" on successive addresses to zero out a block of memory, or would
; call "load" on successive addresses to read a block.  The operation will, of
; course, be slower than what is possible on an MSB implementation, but really
; that's the level of abstraction that we are providing, and it's the level of
; abstraction that we expect users to utilize.  In the future, we might want to
; consider revisiting this decision.

(defthm _address-floor-2
  (implies (and (not (zp depth))
                (_address-p addr depth))
           (_address-p (floor addr 2) (1- depth))))

(defthm _memtree-car/cdr
  (implies (and (not (zp depth))
                (_memtree-p mtree depth))
           (and (_memtree-p (car mtree) (1- depth))
                (_memtree-p (cdr mtree) (1- depth)))))

(defthm _memtree-cons
  (implies (force (not (zp depth)))
           (equal (_memtree-p (cons a b) depth)
                  (and (_memtree-p a (1- depth))
                       (_memtree-p b (1- depth))
                       (or (not (null a))
                           (not (null b)))))))




; Here is our generic load function.  It is simple and easy to reason about,
; but turns out to be pretty lousy at efficiency because of bignum arithmetic,
; but we provide more efficient implementations below.
;
; Note that we could have chosen to short circuit the evaluation, so that if
; mtree is nil, we would immediately return nil.  We choose NOT to do this
; because it would add a nil test on each iteration of the loop, and we think
; that it is unlikely that someone will be frequently loading memory which is
; uninitialized.

(defun _memtree-load (addr mtree depth)
  (declare (xargs :guard (and (natp depth)
                              (_address-p addr depth)
                              (_memtree-p mtree depth))))
  (let ((addr  (_address-fix addr depth))
        (mtree (_memtree-fix mtree depth)))
    (if (zp depth)
        mtree
      (_memtree-load (floor addr 2)
                     (if (= (mod addr 2) 0)
                         (car mtree)
                       (cdr mtree))
                     (1- depth)))))

(defthm _memtree-load-nil
  (equal (_memtree-load addr nil depth)
         nil))



; To make loading faster, we provide enhanced versions below.  The first
; version can be used when addr and depth are both known to be fixnums, and is
; very fast.  However, its application is kind of limited because we will often
; have addresses past the fixnum range, e.g., for 64-bit memories.

(encapsulate
  ()
(local (in-theory (enable signed-byte-p)))

(defun _fix-addr/depth-memtree-load (addr mtree depth)
  (declare (xargs :guard (and (natp depth)
                              (_address-p addr depth)
                              (_memtree-p mtree depth)))
           (type (signed-byte 29) depth)
           (type (signed-byte 29) addr))
  (mbe :logic (_memtree-load addr mtree depth)
       :exec (if (= depth 0)
                 mtree
               (_fix-addr/depth-memtree-load
                (the-fixnum (ash addr -1))
                (if (= (the-fixnum (logand addr 1)) 0)
                    (car mtree)
                  (cdr mtree))
                (the-fixnum (1- depth)))))))



; We would really like to just use the above version, but since we expect our
; addresses to be 64 bits and so forth, it's not really sufficiently general.
; To remedy this, we provide a new function whose only requirement is that
; depth is a fixnum.  The function checks to see if the depth has reached 28
; instead of 0 as its bottom case, and if so it calls our addr/depth-fixnums
; version above.  In other words, the function is "self optimizing" in that it
; will switch over to the very-fast version above as soon as it can do so.

(encapsulate
  ()
  (local (in-theory (enable signed-byte-p)))

  (defun _fixnum-memtree-load (addr mtree depth)
    (declare (xargs :guard (and (natp depth)
                                (_address-p addr depth)
                                (_memtree-p mtree depth)))
             (type (signed-byte 29) depth))
    (mbe :logic (_memtree-load addr mtree depth)
         :exec (if (<= depth 28)
                   (_fix-addr/depth-memtree-load addr mtree depth)
                 (_fixnum-memtree-load (ash addr -1)
                                       (if (= (the-fixnum (logand addr 1)) 0)
                                           (car mtree)
                                         (cdr mtree))
                                       (the-fixnum (1- depth)))))))




; We now provide a store function.  I think this definition is pretty standard
; following from the definition of load.
;
; One interesting aspect is that we require that our element is non-nil.  This
; is because we would really like to keep our trees in a canonical form, where
; "nil" elements are not even stored, and paths to them are not created.  But,
; this function would not preserve this property if we gave it "nil" to store.
; For example, (_memtree-store 0 nil nil 2) = ((nil)) instead of nil, violating
; our notion of canonicality.  Indeed, this creates problems when we try to
; prove properties of the form (store addr (load addr mem) mem) = mem.
;
; To address this, we actually provide a separate function below,
; _memtree-store-nil, for the explicit purpose of storing nils into the tree
; and handling the canonicalization.  This lets us avoid all canonicalization
; overhead on calls of _memtree-store for non-nil elements.

(defun _memtree-store (addr elem mtree depth)
  (declare (xargs :guard (and (natp depth)
                              (not (null elem))
                              (_address-p addr depth)
                              (_memtree-p mtree depth))
                  :measure (acl2-count depth)))
  (let ((addr  (_address-fix addr depth))
        (mtree (_memtree-fix mtree depth)))
    (if (zp depth)
        elem
      (let ((quotient (floor addr 2)))
        (if (= (mod addr 2) 0)
            (cons (_memtree-store quotient elem (car mtree) (1- depth))
                  (cdr mtree))
          (cons (car mtree)
                (_memtree-store quotient elem (cdr mtree)
                                (1- depth))))))))

; As with loading, we create an efficient version that assumes addr and depth
; are fixnums.  This is our "most efficient" store implementation.

(local (in-theory (enable signed-byte-p)))

(defun _fix-addr/depth-memtree-store (addr elem mtree depth)
  (declare (xargs :guard (and (natp depth)
                              (not (null elem))
                              (_address-p addr depth)
                              (_memtree-p mtree depth)))
           (type (signed-byte 29) depth)
           (type (signed-byte 29) addr))
  (mbe :logic (_memtree-store addr elem mtree depth)
       :exec (if (= depth 0)
                 elem
               (let ((quotient (the-fixnum (ash addr -1))))
                 (if (= (the-fixnum (logand addr 1)) 0)
                     (cons (_fix-addr/depth-memtree-store
                            quotient elem (car mtree) (the-fixnum (1- depth)))
                           (cdr mtree))
                   (cons (car mtree)
                         (_fix-addr/depth-memtree-store
                          quotient elem (cdr mtree)
                          (the-fixnum (1- depth)))))))))

; And as before, we create a "self-optimizing" version which drops the
; requirement that addr is a fixnum, and only needs a fixnum depth.

(defun _fixnum-memtree-store (addr elem mtree depth)
  (declare (xargs :guard (and (natp depth)
                              (not (null elem))
                              (_address-p addr depth)
                              (_memtree-p mtree depth)))
           (type (signed-byte 29) depth))
  (mbe :logic (_memtree-store addr elem mtree depth)
       :exec (if (<= depth 28)
                 (_fix-addr/depth-memtree-store addr elem mtree depth)
               (let ((quotient (ash addr -1)))
                 (if (= (the-fixnum (logand addr 1)) 0)
                     (cons (_fixnum-memtree-store
                            quotient elem (car mtree) (the-fixnum (1- depth)))
                           (cdr mtree))
                   (cons (car mtree)
                         (_fixnum-memtree-store
                          quotient elem (cdr mtree)
                          (the-fixnum (1- depth)))))))))


; Now we are ready to implement "memory erasing", that is, storing nils into
; our memory.  We want to keep our trees in canonical format, so we go to some
; lengths to eliminate branches that are no longer needed.

(defun _memtree-store-nil (addr mtree depth)
  (declare (xargs :guard (and (natp depth)
                              (_address-p addr depth)
                              (_memtree-p mtree depth))
                  :measure (acl2-count depth)))
  (let ((addr  (_address-fix addr depth))
        (mtree (_memtree-fix mtree depth)))
    (if (zp depth)
        nil
      (if (atom mtree)
          nil
        (let ((quotient (floor addr 2)))
          (if (= (mod addr 2) 0)
              (let ((left (_memtree-store-nil quotient (car mtree)
                                              (1- depth)))
                    (right (cdr mtree)))
                (if (and (null left) (null right)) ; canonicalize away!
                    nil
                  (cons left right)))
            (let ((left (car mtree))
                  (right (_memtree-store-nil quotient (cdr mtree) (1- depth))))
                (if (and (null left) (null right)) ; canonicalize away!
                    nil
                  (cons left right)))))))))

(defun _fix-addr/depth-memtree-store-nil (addr mtree depth)
  (declare (xargs :guard (and (natp depth)
                              (_address-p addr depth)
                              (_memtree-p mtree depth)))
           (type (signed-byte 29) depth)
           (type (signed-byte 29) addr))
  (mbe :logic (_memtree-store-nil addr mtree depth)
       :exec (if (= depth 0)
                 nil
               (if (null mtree)
                   nil
                 (let ((quotient (the-fixnum (ash addr -1))))
                   (if (= (the-fixnum (logand addr 1)) 0)
                       (let ((left (_fix-addr/depth-memtree-store-nil
                                    quotient (car mtree)
                                    (the-fixnum (1- depth))))
                             (right (cdr mtree)))
                         (if (and (null left)
                                  (null right))
                             nil
                           (cons left right)))
                     (let ((left (car mtree))
                           (right (_fix-addr/depth-memtree-store-nil
                                   quotient (cdr mtree)
                                   (the-fixnum (1- depth)))))
                       (if (and (null left)
                                (null right))
                           nil
                         (cons left right)))))))))

(defun _fixnum-memtree-store-nil (addr mtree depth)
  (declare (xargs :guard (and (natp depth)
                              (_address-p addr depth)
                              (_memtree-p mtree depth)))
           (type (signed-byte 29) depth))
  (mbe :logic (_memtree-store-nil addr mtree depth)
       :exec (if (<= depth 28)
                 (_fix-addr/depth-memtree-store-nil addr mtree depth)
               (if (null mtree)
                   nil
                 (let ((quotient (ash addr -1)))
                   (if (= (the-fixnum (logand addr 1)) 0)
                       (let ((left (_fixnum-memtree-store-nil
                                    quotient (car mtree)
                                    (the-fixnum (1- depth))))
                             (right (cdr mtree)))
                         (if (and (null left)
                                  (null right))
                             nil
                           (cons left right)))
                     (let ((left (car mtree))
                           (right (_fixnum-memtree-store-nil
                                   quotient (cdr mtree)
                                   (the-fixnum (1- depth)))))
                       (if (and (null left)
                                (null right))
                           nil
                         (cons left right)))))))))



(local (in-theory (disable signed-byte-p)))



; We disable the cancel-floor-+ lemma, because it has been rewriting terms of
; the form (floor a 2) to terms of the form (* 1/2 a), and we prefer the floor
; format for this book.

(local (in-theory (disable ACL2::cancel-floor-+)))


;;; Fixing Theorems

; We now provide a litany of theorems which show that our functions behave as
; if their arguments were coerced using our fixing functions.  Using this
; technique, along with our admittedly bizarre definitions above, we are able
; to provide essentially hypothesis-free rewrite rules for our m operations.
;
; This is the same technique used in my ordered sets book in order to enforce
; the non-sets convention, and you can think of these as "a poor man's
; congruence rules".  Take for example _memtree-load-fix-a below, which
; says that the following:
;
; (defthm _memtree-load-fix-addr
;   (equal (_memtree-load (_address-fix a n) m n)
;          (_memtree-load a m n)))
;
; You could imagine that we had instead written something like this:
;
; (defthm _memtree-load-fix-addr-cong
;   (implies (_address-equal a b)
;            (equal (_memtree-load a m n)
;                   (_memtree-load b m n)))
;   :rule-classes :congruence)
;
; Where _address-equal is some ficticious function that checks if two _addresses
; are equal after fixing them.  Of course, we cannot actually introduce such a
; function, at least not as an equivalence relation, because in order to fix
; the _addresses we have to know how many bits they comprise.  In other words,
; _address-equal would need to be a three-input function of a, b, and n.  But
; ACL2 only permits two-input functions to be equivalence relations.

(defthm _address-p-fix-depth
  (equal (_address-p addr (nfix depth))
         (_address-p addr depth)))

(defthm _memtree-p-fix-depth
  (equal (_memtree-p mtree (nfix depth))
         (_memtree-p mtree depth)))



(defthm _address-fix-nfix
  (equal (_address-fix addr (nfix depth))
         (_address-fix addr depth))
  :hints(("Goal" :in-theory (enable _address-fix))))

(defthm _memtree-fix-nfix
  (equal (_memtree-fix mtree (nfix depth))
         (_memtree-fix mtree depth))
  :hints(("Goal" :in-theory (enable _memtree-fix))))


(defthm _memtree-load-fix-depth
  (equal (_memtree-load addr mtree (nfix depth))
         (_memtree-load addr mtree depth))
  :hints(("Goal"
          :in-theory (disable _memtree-fix-nfix)
          :use ((:instance _memtree-fix-nfix)))))

(defthm _memtree-load-fix-tree
  (equal (_memtree-load addr (_memtree-fix mtree depth) depth)
         (_memtree-load addr mtree depth)))

(defthm _memtree-load-fix-addr
  (equal (_memtree-load (_address-fix addr depth) mtree depth)
         (_memtree-load addr mtree depth)))


(defthm _memtree-store-fix-depth
  (equal (_memtree-store addr elem mtree (nfix depth))
         (_memtree-store addr elem mtree depth)))

(defthm _memtree-store-fix-tree
  (equal (_memtree-store addr elem (_memtree-fix mtree depth) depth)
         (_memtree-store addr elem mtree depth)))

(defthm _memtree-store-fix-addr
  (equal (_memtree-store (_address-fix addr depth) elem mtree depth)
         (_memtree-store addr elem mtree depth))
  :hints(("Subgoal *1/3"
          :use (:instance _memtree-store (addr (_address-fix addr depth))))
         ("Subgoal *1/2"
          :use (:instance _memtree-store (addr (_address-fix addr depth))))))


(defthm _memtree-store-nil-fix-depth
  (equal (_memtree-store-nil addr mtree (nfix depth))
         (_memtree-store-nil addr mtree depth)))

(defthm _memtree-store-nil-fix-tree
  (equal (_memtree-store-nil addr (_memtree-fix mtree depth) depth)
         (_memtree-store-nil addr mtree depth)))

(defthm _memtree-store-nil-fix-addr
  (equal (_memtree-store-nil (_address-fix addr depth) mtree depth)
         (_memtree-store-nil addr mtree depth))
  :hints(("Subgoal *1/3"
          :use (:instance _memtree-store-nil (addr (_address-fix addr depth))))
         ("Subgoal *1/2"
          :use (:instance _memtree-store-nil (addr (_address-fix addr depth))))))

(in-theory (disable _address-p _memtree-p))




;;; Key Lemmas: "equivalent" _addresses can be interchanged in stores

; These lemmas needs to stay disabled because they can easily cause loops.  It
; doesn't seem that simple loop stoppers fix the issue, and I'm too lazy to
; figure out a better solution.

(local (defthmd _memtree-store-addr-switch-1
         (implies (equal (_address-fix a depth)
                         (_address-fix b depth))
                  (equal (_memtree-store a elem mtree depth)
                         (_memtree-store b elem mtree depth)))
         :hints(("Goal" :in-theory (disable _memtree-store-fix-addr)
                 :use ((:instance _memtree-store-fix-addr (addr a))
                       (:instance _memtree-store-fix-addr (addr b)))))))

(local (defthmd _memtree-store-addr-switch-2
         (implies (equal (_address-fix a depth)
                         (_address-fix b depth))
                  (equal (_memtree-store-nil a mtree depth)
                         (_memtree-store-nil b mtree depth)))
         :hints(("Goal" :in-theory (disable _memtree-store-nil-fix-addr)
                 :use ((:instance _memtree-store-nil-fix-addr (addr a))
                       (:instance _memtree-store-nil-fix-addr (addr b)))))))

(local (defthmd _memtree-load-addr-switch
         (implies (equal (_address-fix a depth)
                         (_address-fix b depth))
                  (equal (_memtree-load a mtree depth)
                         (_memtree-load b mtree depth)))
         :hints(("Goal" :in-theory (disable _memtree-load-fix-addr)
                 :use ((:instance _memtree-load-fix-addr (addr a))
                       (:instance _memtree-load-fix-addr (addr b)))))))


;;; Theorems: calling _memtree-store(-nil) always produces a _memtree-p object

(encapsulate
 nil

; We first prove a lemma that only considers when all of the inputs are
; well formed with respect to the guards.

 (local (defthmd lemma
          (implies (and (natp depth)
                        (_address-p addr depth)
                        (_memtree-p mtree depth)
                        elem)
                   (_memtree-p (_memtree-store addr elem mtree depth) depth))))


; Now, using our previous _memtree-store-fix rules, we can quickly deduce
; that our property holds for the general case.

 (defthm _memtree-store-memtree-1
   (implies elem
            (_memtree-p (_memtree-store addr elem mtree depth) depth))
   :hints(("Goal"
           :use (:instance lemma
                           (depth (nfix depth))
                           (addr  (_address-fix addr depth))
                           (mtree (_memtree-fix mtree depth))))))


; And we do the same thing for _memtree-store-nil

 (local (defthmd lemma2
          (implies (and (natp depth)
                        (_address-p addr depth)
                        (_memtree-p mtree depth))
                   (_memtree-p (_memtree-store-nil addr mtree depth) depth))))

 (defthm _memtree-store-memtree-2
   (_memtree-p (_memtree-store-nil addr mtree depth) depth)
   :hints(("Goal"
           :use (:instance lemma2
                           (depth (nfix depth))
                           (addr  (_address-fix addr depth))
                           (mtree (_memtree-fix mtree depth))))))
 )




;;; Theorems: reading after writing it gives back the same value

(encapsulate
 nil

; We first prove our theorem for when the inputs are well formed.

 (local (defthmd lemma
          (implies (and (natp depth)
                        (_address-p addr depth)
                        (_memtree-p mtree depth)
                        elem)
                   (equal (_memtree-load addr
                                         (_memtree-store addr elem mtree depth)
                                         depth)
                          elem))
          :hints(("Goal"
                  :induct (_memtree-load addr
                                         (_memtree-store addr elem mtree depth)
                                         depth)))))

; Now using this lemma in conjunction with our "key" _address switching lemma
; above, and our fixing lemmas, we can show how this property holds for the
; general case.  Note the test of (equal (_address-fix a depth) (_address-fix b
; depth)).  It should be easy to see that this is actually more general than
; targetting (_memtree-load a (_memtree-store a elem mtree depth)).

 (defthm _memtree-load-same-store-1
   (implies (and (equal (_address-fix a depth)
                        (_address-fix b depth))
                 elem)
            (equal (_memtree-load a (_memtree-store b elem mtree depth) depth)
                   elem))
   :hints(("Goal"
           :use ((:instance lemma
                            (depth (nfix depth))
                            (addr  (_address-fix a depth))
                            (mtree (_memtree-fix mtree depth)))
                 (:instance _memtree-store-addr-switch-1)))))

; And we do the equivalent thing for storing nil.

 (local (defthmd lemma2
          (implies (and (natp depth)
                        (_address-p addr depth)
                        (_memtree-p mtree depth))
                   (equal (_memtree-load addr
                                         (_memtree-store-nil addr mtree depth)
                                         depth)
                          nil))
          :hints(("Goal"
                  :induct (_memtree-load addr
                                         (_memtree-store-nil addr mtree depth)
                                         depth)))))

 (defthm _memtree-load-same-store-2
   (implies (equal (_address-fix a depth)
                   (_address-fix b depth))
            (equal (_memtree-load a (_memtree-store-nil b mtree depth) depth)
                   nil))
   :hints(("Goal"
           :use ((:instance lemma2
                            (depth (nfix depth))
                            (addr  (_address-fix a depth))
                            (mtree (_memtree-fix mtree depth)))
                 (:instance _memtree-store-addr-switch-2)))))

 )




;;; Theorem: reading an _address after writing a different _address is the
;;; same as reading the _address without having written anything

(encapsulate
 nil

; Again we begin our proof with a lemma for the well formed inputs case.

 (local (defthmd lemma
          (implies (and (natp depth)
                        (_address-p a depth)
                        (_address-p b depth)
                        (_memtree-p mtree depth)
                        (not (equal a b))
                        elem)
                   (equal (_memtree-load a
                                         (_memtree-store b elem mtree depth)
                                         depth)
                          (_memtree-load a mtree depth)))
          :hints(("Goal"
                  :induct (_memtree-load a
                                         (_memtree-store b elem mtree depth)
                                         depth)))))

; Our fixing lemmas can then easily transform this lemma into a proof
; of the general case.

 (defthm _memtree-load-diff-store-1
   (implies (and (not (equal (_address-fix a depth)
                             (_address-fix b depth)))
                 elem)
            (equal (_memtree-load a (_memtree-store b elem mtree depth) depth)
                   (_memtree-load a mtree depth)))
   :hints(("Goal"
           :use (:instance lemma
                           (depth (nfix depth))
                           (a     (_address-fix a depth))
                           (b     (_address-fix b depth))
                           (mtree (_memtree-fix mtree depth))))))

; And again the equivalent thing for store-nil

 (local (defthmd lemma2
          (implies (and (natp depth)
                        (_address-p a depth)
                        (_address-p b depth)
                        (_memtree-p mtree depth)
                        (not (equal a b)))
                   (equal (_memtree-load a
                                         (_memtree-store-nil b mtree depth)
                                         depth)
                          (_memtree-load a mtree depth)))
          :hints(("Goal"
                  :induct (_memtree-load a
                                         (_memtree-store-nil b mtree depth)
                                         depth)))))

 (defthm _memtree-load-diff-store-2
   (implies (not (equal (_address-fix a depth)
                        (_address-fix b depth)))
            (equal (_memtree-load a (_memtree-store-nil b mtree depth) depth)
                   (_memtree-load a mtree depth)))
   :hints(("Goal"
           :use (:instance lemma2
                           (depth (nfix depth))
                           (a     (_address-fix a depth))
                           (b     (_address-fix b depth))
                           (mtree (_memtree-fix mtree depth))))))

 )




;;; Theorems: successive stores to the same address can be cancelled

(encapsulate
 nil

; We first show the theorem for memtree-store using our standard technique.

 (local (defthmd lemma
          (implies (and (natp depth)
                        (_address-p addr depth)
                        (_memtree-p mtree depth)
                        e1
                        e2)
                   (equal (_memtree-store addr e1
                           (_memtree-store addr e2 mtree depth) depth)
                          (_memtree-store addr e1 mtree depth)))
          :hints(("Goal"
                  :induct (_memtree-store addr e1
                           (_memtree-store addr e2 mtree depth)
                           depth)))))

 (defthm _memtree-store-smash-1
   (implies (and (equal (_address-fix a depth)
                        (_address-fix b depth))
                 e1
                 e2)
            (equal (_memtree-store a e1
                    (_memtree-store b e2 mtree depth) depth)
                   (_memtree-store a e1 mtree depth)))
   :hints(("Goal"
           :use ((:instance lemma
                            (depth (nfix depth))
                            (addr  (_address-fix a depth))
                            (mtree (_memtree-fix mtree depth)))
                 (:instance _memtree-store-addr-switch-1 (elem e2))))))


; We also show the theorem for two instances of memtree-store-nil.

 (local (defthmd lemma2
          (implies (and (natp depth)
                        (_address-p addr depth)
                        (_memtree-p mtree depth))
                   (equal (_memtree-store-nil addr
                           (_memtree-store-nil addr mtree depth) depth)
                          (_memtree-store-nil addr mtree depth)))
          :hints(("Goal"
                  :induct (_memtree-store-nil addr
                           (_memtree-store-nil addr mtree depth)
                           depth)))))

 (defthm _memtree-store-smash-2
   (implies (equal (_address-fix a depth)
                   (_address-fix b depth))
            (equal (_memtree-store-nil a
                    (_memtree-store-nil b mtree depth) depth)
                   (_memtree-store-nil a mtree depth)))
   :hints(("Goal"
           :use ((:instance lemma2
                            (depth (nfix depth))
                            (addr  (_address-fix a depth))
                            (mtree (_memtree-fix mtree depth)))
                 (:instance _memtree-store-addr-switch-2)))))


; But we aren't done yet.  We also need to know that memtree-store-nil and
; memtree-store can be interchanged in this manner.

 (local (defthmd lemma3
          (implies (and (natp depth)
                        (_address-p addr depth)
                        (_memtree-p mtree depth)
                        elem)
                   (equal (_memtree-store addr elem
                           (_memtree-store-nil addr mtree depth) depth)
                          (_memtree-store addr elem mtree depth)))
          :hints(("Goal"
                  :induct (_memtree-store addr elem
                           (_memtree-store-nil addr mtree depth)
                           depth)))))

 (defthm _memtree-store-smash-3
   (implies (and (equal (_address-fix a depth)
                        (_address-fix b depth))
                 elem)
            (equal (_memtree-store a elem
                                   (_memtree-store-nil b mtree depth)
                                   depth)
                   (_memtree-store a elem mtree depth)))
   :hints(("Goal"
           :use ((:instance lemma3
                            (depth (nfix depth))
                            (addr  (_address-fix a depth))
                            (mtree (_memtree-fix mtree depth)))
                 (:instance _memtree-store-addr-switch-2)))))

 (local (defthmd lemma4
          (implies (and (natp depth)
                        (_address-p addr depth)
                        (_memtree-p mtree depth)
                        elem)
                   (equal (_memtree-store-nil addr
                           (_memtree-store addr elem mtree depth) depth)
                          (_memtree-store-nil addr mtree depth)))
          :hints(("Goal"
                  :induct (_memtree-store-nil addr
                           (_memtree-store addr elem mtree depth)
                           depth)))))

 (defthm _memtree-store-smash-4
   (implies (and (equal (_address-fix a depth)
                        (_address-fix b depth))
                 elem)
            (equal (_memtree-store-nil a
                                       (_memtree-store b elem mtree depth)
                                       depth)
                   (_memtree-store-nil a mtree depth)))
   :hints(("Goal"
           :use ((:instance lemma4
                            (depth (nfix depth))
                            (addr  (_address-fix a depth))
                            (mtree (_memtree-fix mtree depth)))
                 (:instance _memtree-store-addr-switch-1)))))

 )



;;; Theorem: stores to different locations can be reordered

(encapsulate
 nil

; We begin with two lemmas that will help ACL2 open up terms in our main lemma
; more intelligently.

 (local (defthm odd-lemma
          (implies (and (not (zp depth))
                        (_address-p addr depth)
                        (_memtree-p mtree depth)
                        (equal (mod addr 2) 1)
                        elem)
                   (equal (_memtree-store addr elem mtree depth)
                          (cons (car mtree)
                                (_memtree-store (floor addr 2)
                                                elem
                                                (cdr mtree)
                                                (1- depth)))))
          :hints(("Goal" :expand (_memtree-store addr elem mtree depth)))))

 (local (defthm even-lemma
          (implies (and (not (zp depth))
                        (_address-p addr depth)
                        (_memtree-p mtree depth)
                        (equal (mod addr 2) 0)
                        elem)
                   (equal (_memtree-store addr elem mtree depth)
                          (cons (_memtree-store (floor addr 2)
                                                elem
                                                (car mtree)
                                                (1- depth))
                                (cdr mtree))))
          :hints(("Goal" :expand (_memtree-store addr elem mtree depth)))))


; Here is our main lemma.  We show that our property holds as long as all of
; the inputs are well formed.

 (local (defthmd main-lemma
          (implies (and (natp depth)
                        (_address-p a depth)
                        (_address-p b depth)
                        (_memtree-p mtree depth)
                        (not (equal a b))
                        e1 e2)
                   (equal (_memtree-store a e1
                           (_memtree-store b e2 mtree depth) depth)
                          (_memtree-store b e2
                           (_memtree-store a e1 mtree depth) depth)))
          :hints(("Goal"
                  :induct (_memtree-store a e1
                           (_memtree-store b e2 mtree depth)
                           depth)))))


; Now it's just a simple matter of generalizing this to include bad inputs.

 (defthm _memtree-store-reorder-1
   (implies (and (not (equal (_address-fix a depth)
                             (_address-fix b depth)))
                 e1 e2)
            (equal (_memtree-store a e1
                    (_memtree-store b e2 mtree depth) depth)
                   (_memtree-store b e2
                    (_memtree-store a e1 mtree depth) depth)))
   :hints(("Goal"
           :use (:instance main-lemma
                           (depth (nfix depth))
                           (a     (_address-fix a depth))
                           (b     (_address-fix b depth))
                           (mtree (_memtree-fix mtree depth))))))


; And now we do the analagous thing for storing nil

 (local (defthm odd-lemma-2
          (implies (and (equal (mod addr 2) 1)
                        (not (zp depth))
                        (_address-p addr depth)
                        (_memtree-p mtree depth))
                   (equal (_memtree-store-nil addr mtree depth)
                          (if (atom mtree)
                              nil
                            (let ((left (car mtree))
                                  (right (_memtree-store-nil (floor addr 2)
                                                             (cdr mtree)
                                                             (1- depth))))
                              (if (and (null left)
                                       (null right))
                                  nil
                                (cons left right))))))
          :hints(("Goal" :use (:instance _memtree-store-nil)))))

 (local (defthm even-lemma-2
          (implies (and (equal (mod addr 2) 0)
                        (not (zp depth))
                        (_address-p addr depth)
                        (_memtree-p mtree depth))
                   (equal (_memtree-store-nil addr mtree depth)
                          (if (atom mtree)
                              nil
                            (let ((left (_memtree-store-nil (floor addr 2)
                                                            (car mtree)
                                                            (1- depth)))
                                  (right (cdr mtree)))
                              (if (and (null left)
                                       (null right))
                                  nil
                                (cons left right))))))
          :hints(("Goal" :use (:instance _memtree-store-nil)))))


 (local (defthmd main-lemma-2
          (implies (and (not (equal a b))
                        (natp depth)
                        (_address-p a depth)
                        (_address-p b depth)
                        (_memtree-p mtree depth))
                   (equal (_memtree-store-nil a
                                              (_memtree-store-nil b mtree depth)
                                              depth)
                          (_memtree-store-nil b
                                              (_memtree-store-nil a mtree depth)
                                              depth)))
          :hints(("Goal"
                  :induct (_memtree-store-nil a
                                              (_memtree-store-nil b mtree depth)
                                              depth)))))

 (defthm _memtree-store-reorder-2
   (implies (not (equal (_address-fix a depth)
                        (_address-fix b depth)))
            (equal (_memtree-store-nil a
                                       (_memtree-store-nil b mtree depth)
                                       depth)
                   (_memtree-store-nil b
                                       (_memtree-store-nil a mtree depth)
                                       depth)))
   :hints(("Goal"
           :use (:instance main-lemma-2
                           (depth (nfix depth))
                           (a     (_address-fix a depth))
                           (b     (_address-fix b depth))
                           (mtree (_memtree-fix mtree depth))))))


 (local (defthm _memtree-store-not-nil
          (equal (equal (_memtree-store addr elem mtree depth) nil)
                 (and (zp depth)
                      (null elem)))))

 (local (defthm _memtree-store-car
          (implies (and (not (zp depth))
                        (_address-p addr depth)
                        (_memtree-p mtree depth))
                   (equal (car (_memtree-store addr elem mtree depth))
                          (if (equal (mod addr 2) 0)
                              (_memtree-store (floor addr 2)
                                              elem
                                              (car mtree)
                                              (1- depth))
                            (car mtree))))
          :hints(("Goal" :expand (_memtree-store addr elem mtree depth)))))

 (local (defthm _memtree-store-cdr
          (implies (and (not (zp depth))
                        (_address-p addr depth)
                        (_memtree-p mtree depth))
                   (equal (cdr (_memtree-store addr elem mtree depth))
                          (if (equal (mod addr 2) 1)
                              (_memtree-store (floor addr 2)
                                              elem
                                              (cdr mtree)
                                              (1- depth))
                            (cdr mtree))))
          :hints(("Goal" :expand (_memtree-store addr elem mtree depth)))))


 (local (defthm zp-addr-lemma
          (implies (and (zp depth)
                        (_address-p a depth)
                        (_address-p b depth))
                   (equal (equal a b) t))
          :hints(("Goal" :in-theory (enable _address-p)))))

 (local (defthm mtree-zero-lemma
          (implies (and (not (zp depth))
                        (not (consp mtree))
                        (_memtree-p mtree depth))
                   (equal mtree nil))
          :hints(("Goal" :in-theory (enable _memtree-p)))
          :rule-classes ((:forward-chaining
                          :trigger-terms ((_memtree-p mtree depth))))))


 (local (defthm main-lemma3-helper
          (implies (and (_address-p a depth)
                        (_address-p b depth)
                        (not (equal a b))
                        elem)
                   (equal (_memtree-store-nil b
                                              (_memtree-store a elem nil depth)
                                              depth)
                          (_memtree-store a elem nil depth)))))

 (local (defthmd main-lemma-3
          (implies (and (natp depth)
                        (_address-p a depth)
                        (_address-p b depth)
                        (_memtree-p mtree depth)
                        (not (equal a b))
                        elem)
                   (equal (_memtree-store a elem
                                          (_memtree-store-nil b mtree depth)
                                          depth)
                          (_memtree-store-nil b
                                              (_memtree-store a elem mtree depth)
                                              depth)))
          :hints(("Goal"
                  :induct (_memtree-store a elem
                                          (_memtree-store-nil b mtree depth)
                                          depth)))))


 (defthm _memtree-store-reorder-3
   (implies (and (not (equal (_address-fix a depth)
                             (_address-fix b depth)))
                 elem)
            (equal (_memtree-store a elem
                                   (_memtree-store-nil b mtree depth)
                                   depth)
                   (_memtree-store-nil b
                                       (_memtree-store a elem mtree depth)
                                       depth)))
   :hints(("Goal"
           :use (:instance main-lemma-3
                           (depth (nfix depth))
                           (a     (_address-fix a depth))
                           (b     (_address-fix b depth))
                           (mtree (_memtree-fix mtree depth))))))

 )



;;; Theorem: storing the contents of some address in that same address does not
;;; change the memory.

(encapsulate
 nil

 (local (defthmd lemma
          (implies (and (natp depth)
                        (_memtree-p mtree depth)
                        (_address-p addr depth)
                        (_memtree-load addr mtree depth))
                   (equal (_memtree-store addr (_memtree-load addr mtree depth)
                                          mtree depth)
                          mtree))))

 (defthm _memtree-store-same-load
   (implies (and (equal (_address-fix a depth)
                        (_address-fix b depth))
                 (_memtree-load a mtree depth))
            (equal (_memtree-store a (_memtree-load b mtree depth)
                                   mtree depth)
                   (_memtree-fix mtree depth)))
   :hints(("Goal"
           :use ((:instance lemma
                            (depth (nfix depth))
                            (addr  (_address-fix a depth))
                            (mtree (_memtree-fix mtree depth)))
                 (:instance _memtree-load-addr-switch
                            (a b)
                            (b a))))))


 (local (defthm mtree-zero-lemma
          (implies (and (not (zp depth))
                        (not (consp mtree))
                        (_memtree-p mtree depth))
                   (equal mtree nil))
          :hints(("Goal" :in-theory (enable _memtree-p)))
          :rule-classes ((:forward-chaining
                          :trigger-terms ((_memtree-p mtree depth))))))

 (local (defthmd lemma2
          (implies (and (natp depth)
                        (_memtree-p mtree depth)
                        (_address-p addr depth)
                        (not (_memtree-load addr mtree depth)))
                   (equal (_memtree-store-nil addr mtree depth)
                          (_memtree-fix mtree depth)))
          :hints(("Goal" :induct (_memtree-store-nil addr mtree depth)))))

 (defthm _memtree-store-same-load-nil
   (implies (and (equal (_address-fix a depth)
                        (_address-fix b depth))
                 (not (_memtree-load a mtree depth)))
            (equal (_memtree-store-nil a mtree depth)
                   (_memtree-fix mtree depth)))
   :hints(("Goal"
           :use ((:instance lemma2
                            (depth (nfix depth))
                            (addr  (_address-fix a depth))
                            (mtree (_memtree-fix mtree depth)))
                 (:instance _memtree-load-addr-switch
                            (a b)
                            (b a))))))

 )

