; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
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

; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility
(error "is anyone using this?  If so please remove this message.")

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; records-definitions.lisp
;; John D. Powell
;(in-package "RECORDS")

;;
;; This file isolates records definitions and types. The file currently
;; contains the following ACL2 constructs as they occur in the records book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

; For write tests we will just zero out a block of memory.  It doesn't really
; matter what addresses we use, because they're all the same depth from the
; root.  For read tests, we'll just sequentially scan a block of memory.

(defun zero-memory (i mem)
  (declare (xargs :guard (and (memory-p mem)
                              (address-p i mem)))
           (type (signed-byte 29) i))
  (if (mbe :logic (zp i)
           :exec (= i 0))
      (store 0 0 mem)
    (zero-memory (the-fixnum (1- i))
                 (store i 0 mem))))

(defun scan-memory (i mem)
  (declare (xargs :guard (and (memory-p mem)
                              (address-p i mem)))
           (type (signed-byte 29) i))
  (if (mbe :logic (zp i)
           :exec (= i 0))
      (load 0 mem)
    (let ((element (load i mem)))
      (declare (ignore element))
      (scan-memory (the-fixnum (1- i)) mem))))

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
  (declare (xargs :guard (and (natp depth)
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
  (declare (xargs :guard (and (natp depth)
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
                (the-fixnum (1- depth))))))



; We would really like to just use the above version, but since we expect our
; addresses to be 64 bits and so forth, it's not really sufficiently general.
; To remedy this, we provide a new function whose only requirement is that
; depth is a fixnum.  The function checks to see if the depth has reached 28
; instead of 0 as its bottom case, and if so it calls our addr/depth-fixnums
; version above.  In other words, the function is "self optimizing" in that it
; will switch over to the very-fast version above as soon as it can do so.

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
                                     (the-fixnum (1- depth))))))




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

(defun _memory-p (mem)
  (and (consp mem)
       (consp (car mem))
       (consp (cdr mem))
       (consp (cddr mem))
       (let ((mtree  (caar mem))
             (fast   (cdar mem))
             (size   (cadr mem))
             (depth  (caddr mem)))
         (and (natp size)
              (natp depth)
              (booleanp fast)
              (implies fast (signed-byte-p 29 depth))
              (<= size (expt 2 depth))
              (_memtree-p mtree depth)))))

; We implement a typical fixing function for memories.  Our default memory is
; an empty tree with size 1 and depth 1.

(defun _memory-fix (mem)
  (declare (xargs :guard (_memory-p mem)))
  (if (mbt (_memory-p mem))
      mem
    (list* (cons nil t) 0 0 nil)))

(defthm _memory-fix-memory
  (_memory-p (_memory-fix mem)))

(defthm _memory-fix-identity
  (implies (_memory-p mem)
           (equal (_memory-fix mem) mem)))


; And we implement basic accessors for our memory structures.  Note that the
; user is only expected to be interested in the 'size' field, and should not
; particularly know/care about the underlying memtree and depth fields.

(defun _memory-size (mem)
  (declare (xargs :guard (_memory-p mem)))
  (cadr (_memory-fix mem)))

(defthm _memory-size-natural
  (and (integerp (_memory-size mem))
       (<= 0 (_memory-size mem)))
  :rule-classes :type-prescription)

(defun _memory-fast (mem)
  (declare (xargs :guard (_memory-p mem)))
  (cdar (_memory-fix mem)))

(defthm _memory-fast-bool
  (or (equal (_memory-fast mem) t)
      (equal (_memory-fast mem) nil))
  :rule-classes :type-prescription)

(defun _memory-depth (mem)
  (declare (xargs :guard (_memory-p mem)))
  (caddr (_memory-fix mem)))

(defthm _memory-depth-positive
  (and (integerp (_memory-depth mem))
       (<= 0 (_memory-depth mem)))
  :rule-classes :type-prescription)

(defthm _memory-depth-signed-byte
  (implies (_memory-fast mem)
           (signed-byte-p 29 (_memory-depth mem))))

(defthm _memory-mtree-length/depth
  (<= (_memory-size mem)
      (expt 2 (_memory-depth mem)))
  :rule-classes :linear)

(defun _memory-mtree (mem)
  (declare (xargs :guard (_memory-p mem)))
  (caar (_memory-fix mem)))

(defthm _memory-mtree-memtree
  (_memtree-p (_memory-mtree mem)
              (_memory-depth mem)))

(defthm _memory-mtree-count
  (implies (_memory-p x)
           (< (acl2-count (_memory-mtree x))
              (acl2-count x)))
  :rule-classes :linear)

(defun _memory-record (mem)
  (declare (xargs :guard (_memory-p mem)))
  (cdddr (_memory-fix mem)))

(defthm _memory-equal
  (implies (and (_memory-p a)
                (_memory-p b))
           (equal (equal a b)
                  (and (equal (_memory-mtree a)  (_memory-mtree b))
                       (equal (_memory-size a)   (_memory-size b))
                       (equal (_memory-depth a)  (_memory-depth b))
                       (equal (_memory-fast a)   (_memory-fast b))
                       (equal (_memory-record a) (_memory-record b))))))

(defthm _memory-mtree-bad
  (implies (not (_memory-p mem))
           (equal (_memory-mtree mem) nil)))

(defthm _memory-size-bad
  (implies (not (_memory-p mem))
           (equal (_memory-size mem) 0)))

(defthm _memory-fast-bad
  (implies (not (_memory-p mem))
           (equal (_memory-fast mem) t)))

(defthm _memory-depth-bad
  (implies (not (_memory-p mem))
           (equal (_memory-depth mem) 0)))

(defthm _memory-record-bad
  (implies (not (_memory-p mem))
           (equal (_memory-record mem) nil)))

(in-theory (disable _memory-depth
                    _memory-mtree
                    _memory-fast
                    _memory-record
                    _memory-size))

; We now begin implementing the trick developed by Rob Sumners and Matt
; Kaufmann in their records book.  The 2002 Workshop paper, "Efficient
; Rewriting of Operations on Finite Structures in ACL2" is useful for
; understanding what is going on.  In fact, at the beginning of Section 4, they
; give a multi-step process for removing hyptheses:
;
;  (1) determine a normal form for the data structure such that "equivalent"
;  structures are equal.
;
;  (2) define the desired operations assuming well formed data structures (we
;  already did this too, our load and store operations)
;
;  (3) prove the desired theorems about the operations, assuming well-formed
;  data structures.  This leads to equal-based theorems with some hypotheses
;  about the normalized or well-formed objects.
;
;  (4) define an invertible mapping from ACL2 objects into well-formed objects
;
;  (5) define "translated" versions from the "nice" operations from (2) using
;  the mapping and inverse to translate ACL2 objects into well formed objects
;  and back.
;
;  (6) prove the desired properties about the "translated" operations removing
;  the well-formed hypotheses.
;
; Below, we begin work on (4), that is, we are interested in defining an
; invertible mapping between ACL2 objects and memories.  We define a bad memory
; as anything that is not a memory, or any memory whose depth and size are zero
; and whose mtree is also a bad memory.  These are our equivalent of Sumners
; and Kaufmann's "ifrp" (ill formed record) objects.  We will then provide
; to-mem and from-mem mappings.

(defun _bad-memory-p (x)
  (or (not (_memory-p x))
      (and (equal (_memory-fast x) t)
           (equal (_memory-depth x) 0)
           (equal (_memory-size x) 0)
           (equal (_memory-record x) nil)
           (_bad-memory-p (_memory-mtree x)))))

(in-theory (disable _memory-p))

(defun _to-mem (x)
  (if (_bad-memory-p x)
      (list* (cons x t) 0 0 nil)
    x))

(defthm _to-mem-record
  (implies (_bad-memory-p x)
           (equal (_memory-record (_to-mem x)) nil))
  :hints(("Goal" :in-theory (enable _memory-record))))

(defthm _to-mem-depth
  (implies (_bad-memory-p x)
           (equal (_memory-depth (_to-mem x)) 0))
  :hints(("Goal" :in-theory (enable _memory-depth))))

(defthm _to-mem-size
  (implies (_bad-memory-p x)
           (equal (_memory-size (_to-mem x)) 0))
  :hints(("Goal" :in-theory (enable _memory-size))))

(defthm _to-mem-fast
  (implies (_bad-memory-p x)
           (equal (_memory-fast (_to-mem x)) t))
  :hints(("Goal" :in-theory (enable _memory-fast))))

(defthm _to-mem-mtree
  (implies (_bad-memory-p x)
           (equal (_memory-mtree (_to-mem x))
                  x))
  :hints(("Goal" :in-theory (enable _memory-mtree _memory-p))))

(defthm _to-mem-memory
  (_memory-p (_to-mem x))
  :hints(("Goal" :in-theory (enable _memory-p))))

(defthm _to-mem-ifmem
  (equal (_bad-memory-p (_to-mem x))
         (_bad-memory-p x))
  :hints(("Goal" :in-theory (enable _memory-fast
                                    _memory-depth
                                    _memory-record
                                    _memory-mtree
                                    _memory-size))))

(defthm _to-mem-identity
  (implies (not (_bad-memory-p x))
           (equal (_to-mem x) x)))

(in-theory (disable _to-mem))


(defun _from-mem (x)
  (declare (xargs :guard (_memory-p x)))
  (if (_bad-memory-p x)
      (_memory-mtree x)
    x))

(defthm _from-mem-record
  (implies (_bad-memory-p x)
           (equal (_memory-record (_from-mem x)) nil)))

(defthm _from-mem-depth
  (implies (_bad-memory-p x)
           (equal (_memory-depth (_from-mem x)) 0)))

(defthm _from-mem-size
  (implies (_bad-memory-p x)
           (equal (_memory-size (_from-mem x)) 0)))

(defthm _from-mem-fast
  (implies (_bad-memory-p x)
           (equal (_memory-fast (_from-mem x)) t)))

(defthm _from-mem-mtree
  (implies (_bad-memory-p x)
           (equal (_memory-mtree (_from-mem x))
                  (_memory-mtree (_memory-mtree x)))))

(defthm _from-mem-identity
  (implies (not (_bad-memory-p x))
           (equal (_from-mem x)
                  x)))

(defthm _from/to-memory-lemma
  (implies (_memory-p mem)
           (_memory-p (_from-mem (_to-mem mem)))))

(defthm _from/to-inverse
  (equal (_from-mem (_to-mem mem)) mem))

(defthm _to/from-inverse
  (implies (_memory-p mem)
           (equal (_to-mem (_from-mem mem)) mem)))

(in-theory (disable _from-mem))

; Publically Visible Definition of Memories
;
; Below is the "user's notion" of what a memory is.  It should always be
; disabled.  Basically, we require that a user's memory is always has a depth
; and size of at least one.
;
; This gives us the crucial property that "bad memories" are not memories in
; the user's sense.  Why is this so important?  Well, we are very much
; concerned with efficiency of operations.  As long as we know that our
; arguments are not bad, we can skip all of this mapping and just provide
; high speed execution using MBE.

(defun memory-p (mem)
  (and (_memory-p mem)
       (posp (_memory-size mem))
       (posp (_memory-depth mem))))

(defthm memory-p-bool
  (or (equal (memory-p mem) t)
      (equal (memory-p mem) nil))
  :rule-classes :type-prescription)

(defthm _bad-memories-not-recognized
  (implies (_bad-memory-p mem)
           (not (memory-p mem))))

(defthm _bad-memories-not-recognized-2
  (implies (memory-p mem)
           (not (_bad-memory-p mem))))

(defun size (mem)
  (declare (xargs :guard (memory-p mem)
                  :guard-hints (("Goal" :in-theory (enable _memory-size)))))
  (mbe :logic (if (memory-p mem)
                  (_memory-size mem)
                1)
       :exec (cadr mem)))

(defthm size-positive
  (and (integerp (size m))
       (< 0 (size m)))
  :rule-classes :type-prescription)

; Memory Addresses.  Addresses should be naturals that are less than the size
; of the memory.

(defun address-p (addr mem)
  (declare (xargs :guard (memory-p mem)))
  (and (natp addr)
       (< addr (size mem))))

(defthm _address-from-address
  (implies (address-p addr mem)
           (_address-p addr (_memory-depth mem)))
  :hints(("Goal" :in-theory (enable _address-p))))

; Memory Creation.  We want to allow the user to create a new memory just using
; (new 600) and so forth.  The user should not need to consider the depth of
; the tree needed -- they should just say how many elements they want.  Well,
; then, we have to take the base-2 log of the size they give us.

(defun new (size)
  (declare (xargs :guard (posp size)))
  (if (or (not (posp size))
          (equal size 1))
      (cons (cons nil t) (cons 1 (cons 1 nil)))
    (let ((depth (_log2 (1- size))))
      (cons
       (cons nil (signed-byte-p 29 depth))
       (cons size
             (cons depth nil))))))

(defthm _new-memory
  (_memory-p (new size))
  :hints(("Goal" :in-theory (enable _memory-p))))

(defthm new-memory
  (memory-p (new size))
  :hints(("Goal"
          :in-theory (enable _memory-p
                             _memory-size
                             _memory-depth))))

(defthm _new-mtree
  (equal (_memory-mtree (new size))
         nil)
  :hints(("Goal" :in-theory (enable _memory-mtree))))

(defthm _new-record
  (equal (_memory-record (new size))
         nil)
  :hints(("Goal" :in-theory (enable _memory-record))))

(defthm _new-size
  (equal (_memory-size (new size))
         (if (posp size)
             size
           1))
  :hints(("Goal" :in-theory (enable _memory-size _memory-p))))

(defthm new-size
  (equal (size (new size))
         (if (posp size)
             size
           1))
  :hints(("Goal" :in-theory (disable new))))

(local (in-theory (disable new)))

(defun _load (addr mem)
  (declare (xargs :guard (and (memory-p mem)
                              (address-p addr mem))
                  :guard-hints (("Goal" :in-theory (enable _memory-p
                                                           _memory-mtree
                                                           _memory-fast
                                                           _memory-depth)
                                 :use (:instance _address-from-address)))))
  (mbe :logic (let ((mtree (_memory-mtree mem))
                    (depth (_memory-depth mem))
                    (record (_memory-record mem)))
                (if (address-p addr mem)
                    (_memtree-load addr mtree depth)
                  (g addr record)))
       :exec (let* ((fast (cdar mem))
                    (mtree (caar mem))
                    (depth (caddr mem)))
               (if fast
                   (_fixnum-memtree-load addr mtree depth)
                 (_memtree-load addr mtree depth)))))

(defun _store (addr elem mem)
  (declare (xargs :guard (and (memory-p mem)
                              (address-p addr mem))
                  :guard-hints (("Goal"
                                 :use (:instance _address-from-address)
                                 :in-theory (enable _memory-p
                                                    _memory-mtree
                                                    _memory-fast
                                                    _memory-depth
                                                    _memory-record
                                                    _memory-size)))))
  (mbe :logic (let ((fast   (_memory-fast mem))
                    (mtree  (_memory-mtree mem))
                    (size   (_memory-size mem))
                    (depth  (_memory-depth mem))
                    (record (_memory-record mem)))
                (if (address-p addr mem)
                    (cons (cons (if elem
                                    (_memtree-store addr elem mtree depth)
                                  (_memtree-store-nil addr mtree depth))
                                fast)
                          (cons size (cons depth record)))
                  (cons (cons mtree fast)
                        (cons size (cons depth (s addr elem record))))))
       :exec (let* ((mtree  (caar mem))
                    (fast   (cdar mem))
                    (memcdr (cdr mem))
                    (depth  (cadr memcdr)))
               (cons (cons (if fast
                               (if elem
                                   (_fixnum-memtree-store addr elem mtree depth)
                                 (_fixnum-memtree-store-nil addr mtree depth))
                             (if elem
                                 (_memtree-store addr elem mtree depth)
                               (_memtree-store-nil addr mtree depth)))
                           fast)
                     memcdr))))

(defthm _load-new
  (equal (_load addr (new size))
         nil))

(in-theory (disable signed-byte-p))

(defthm _store-size
  (equal (_memory-size (_store addr elem mem))
         (_memory-size mem))
  :hints(("Goal" :in-theory (e/d (_memory-size)
                                 (_store-memory))
          :use (:instance _store-memory))))

(defthm _store-fast
  (equal (_memory-fast (_store addr elem mem))
         (_memory-fast mem))
  :hints(("Goal" :in-theory (e/d (_memory-fast)
                                 (_store-memory))
          :use (:instance _store-memory))))

(defthm _store-mtree
  (equal (_memory-mtree (_store addr elem mem))
         (if (address-p addr mem)
             (if elem
                 (_memtree-store addr elem
                                 (_memory-mtree mem)
                                 (_memory-depth mem))
               (_memtree-store-nil addr
                                   (_memory-mtree mem)
                                   (_memory-depth mem)))
           (_memory-mtree mem)))
  :hints(("Goal" :in-theory (e/d (_memory-mtree)
                                 (_store-memory))
          :use (:instance _store-memory))))

(defthm _store-depth
  (equal (_memory-depth (_store addr elem mem))
         (_memory-depth mem))
  :hints(("Goal" :in-theory (e/d (_memory-depth)
                                 (_store-memory))
          :use (:instance _store-memory))))

(defthm _store-record
  (equal (_memory-record (_store addr elem mem))
          (if (address-p addr mem)
              (_memory-record mem)
            (s addr elem (_memory-record mem))))
  :hints(("Goal" :in-theory (e/d (_memory-record)
                                 (_store-memory))
          :use (:instance _store-memory))))

(in-theory (disable _store))

(defthm _store-memory-main
  (equal (memory-p (_store addr elem mem))
         (memory-p mem)))

(defthm _store-size-main
  (equal (size (_store addr elem mem))
         (size mem)))

; At this point, we are ever so close to proving everything we want.  Here
; are the nice theorems we can show:

(defthm _load-same-store
  (equal (_load a (_store a elem mem))
         elem))

(defthm _load-diff-store
  (implies (not (equal a b))
           (equal (_load a (_store b elem mem))
                  (_load a mem))))

(defthm _store-smash
  (equal (_store a e1 (_store a e2 mem))
         (_store a e1 mem)))

(defthm _store-reorder
  (implies (not (equal a b))
           (equal (_store a e1 (_store b e2 mem))
                  (_store b e2 (_store a e1 mem)))))

(defthm _store-same-load
  (implies (_memory-p mem)
           (equal (_store a (_load a mem) mem)
                  mem))
  :hints(("Goal" :in-theory (disable _memtree-store-same-load-nil)
          :use (:instance _memtree-store-same-load-nil
                          (a a)
                          (b a)
                          (depth (_memory-depth mem))
                          (mtree (_memory-mtree mem))))))




(defun load (addr mem)
  (declare (xargs :guard (and (memory-p mem)
                              (address-p addr mem))
                  :guard-hints(("Goal" :in-theory (enable _memory-p
                                                          _memory-mtree
                                                          _memory-fast
                                                          _memory-depth)
                                :use (:instance _address-from-address)))))
  (mbe :logic (_load addr (_to-mem mem))
       :exec  (let* ((fast (cdar mem))
                     (mtree (caar mem))
                     (depth (caddr mem)))
                (if fast
                    (_fixnum-memtree-load addr mtree depth)
                  (_memtree-load addr mtree depth)))))

(defun store (addr elem mem)
  (declare (xargs :guard (and (memory-p mem)
                              (address-p addr mem))
                  :guard-hints(("Goal"
                                :use (:instance _address-from-address)
                                :in-theory (enable _memory-p
                                                   _memory-mtree
                                                   _memory-fast
                                                   _memory-depth
                                                   _memory-record
                                                   _memory-size)))))
  (mbe :logic (_from-mem (_store addr elem (_to-mem mem)))
       :exec (let* ((mtree  (caar mem))
                    (fast   (cdar mem))
                    (memcdr (cdr mem))
                    (depth  (cadr memcdr)))
               (cons (cons (if fast
                               (if elem
                                   (_fixnum-memtree-store addr elem mtree depth)
                                 (_fixnum-memtree-store-nil addr mtree depth))
                             (if elem
                                 (_memtree-store addr elem mtree depth)
                               (_memtree-store-nil addr mtree depth)))
                           fast)
                     memcdr))))

(in-theory (disable _load _store))

(defthm load-same-store
  (equal (load a (store a elem mem))
         elem))

(defthm load-diff-store
  (implies (not (equal a b))
           (equal (load a (store b elem mem))
                  (load a mem))))

(defthm store-smash
  (equal (store a e1 (store a e2 mem))
         (store a e1 mem)))

(defthm store-reorder
  (implies (not (equal a b))
           (equal (store a e1 (store b e2 mem))
                  (store b e2 (store a e1 mem)))))

(defthm store-same-load
  (equal (store a (load a mem) mem)
         mem))

;;; That's the main record lemmas.  Now we want to add our own guard lemmas.

(defthm load-new
  (equal (load addr (new size))
         nil))

(defthm store-memory
  (implies (memory-p mem)
           (memory-p (store addr elem mem))))

(defthm store-size
  (implies (memory-p mem)
           (equal (size (store addr elem mem))
                  (size mem))))

(defun _log2-tr (n acc)
  (declare (xargs :guard (and (natp n)
                              (natp acc))))
  (if (zp n)
      acc
    (_log2-tr (mbe :logic (floor n 2)
                   :exec (ash n -1))
              (1+ acc))))

(defun _log2 (n)
  (declare (xargs :guard (natp n)
                  :verify-guards nil))
  (mbe :logic (if (zp n)
                  0
                (1+ (_log2 (floor n 2))))
       :exec (_log2-tr n 0)))

(defthm _log2-equiv
  (implies (and (natp n)
                (natp acc))
           (equal (_log2-tr n acc)
                  (+ (_log2 n) acc))))

(defthm _log2-natural
  (and (integerp (_log2 n))
       (<= 0 (_log2 n)))
  :rule-classes :type-prescription)

(defthm _log2-positive
  (implies (and (integerp n)
                (< 0 n))
           (and (integerp (_log2 n))
                (< 0 (_log2 n))))
  :rule-classes :type-prescription)

(defthm _log2-expt-nat
  (implies (natp n)
           (< n (expt 2 (_log2 n))))
  :rule-classes :linear)

(defthm _log2-expt-pos
  (implies (posp n)
           (<= n (expt 2 (_log2 (1- n)))))
  :rule-classes :linear)

; THEOREMS
;
; Users of the library should base their work on the following theormes.  First
; we note that memory-p is a boolean-valued function, "new" always creates a
; memory-p object, and "store" always produces a memory-p object if it was
; given one to begin with.

(defthm memory-p-bool
  (or (equal (memory-p mem) t)
      (equal (memory-p mem) nil))
  :rule-classes :type-prescription)

(defthm new-memory
  (memory-p (new size)))

(defthm store-memory
  (implies (memory-p mem)
           (memory-p (store addr elem mem))))



; We also observe that the size of a memory is always a positive number,
; creating a new memory always gives a memory that has the desired size (or 1
; if the stated size is invalid), and that storing into a memory does not
; change its size.

(defthm size-positive
  (and (integerp (size m))
       (< 0 (size m)))
  :rule-classes :type-prescription)

(defthm new-size
  (equal (size (new size))
         (if (posp size)
             size
           1)))

(defthm store-size
  (implies (memory-p mem)
           (equal (size (store addr elem mem))
                  (size mem))))



; We also note that upon creation, the value of every address in a memory
; happens to be nil.

(defthm load-new
  (equal (load addr (new size))
         nil))



; Finally, we give the classic record lemmas.  As with the records book, we
; have gone to great lengths to make these hypothesis free, so your rewriting
; should never be burdened with extra hypotheses.  Of course, our rules are
; more strongly guarded than the records book, so you may need to work harder
; on guard verification to get the speed benefits we have to offer.

(defthm load-same-store
  (equal (load a (store a elem mem))
         elem))

(defthm load-diff-store
  (implies (not (equal a b))
           (equal (load a (store b elem mem))
                  (load a mem))))

(defthm store-smash
  (equal (store a e1 (store a e2 mem))
         (store a e1 mem)))

(defthm store-reorder
  (implies (not (equal a b))
           (equal (store a e1 (store b e2 mem))
                  (store b e2 (store a e1 mem))))

(defthm store-same-load
  (equal (store a (load a mem) mem)
         mem))

(defun index_list_rec (base off size)
  (if (zp size) nil
    (cons (ifix (+ base off))
          (index_list_rec base (1+ off) (1- size)))))

(defthm integer-list-p-index_list_rec
  (integer-list-p (index_list_rec base off size))
  :hints (("goal" :in-theory (enable integer-listp))))

(defun index_list (base size)
  (index_list_rec base 0 size))

(defthm integer-list-p-index_list
  (integer-list-p (index_list base size)))

(defun default-integer-list-list () nil)

(defun integer-list-list-p (list)
  (declare (type t list))
  (if (consp list)
      (and (integer-listp (car list))
           (integer-list-list-p (cdr list)))
    (null list)))

(in-theory (disable index_list))

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|                                                                           |#
#|                                                                           |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|

Typed records in ACL2

This file contains an enhancement to the ACL2 standard "records" book.
We introduce the macro "defrecord" to define an accessor and updater
function for a record structure with elements of a particular type.
This facility extends somewhat the hypothesis-less theorems of the
standard ACL2 "records" book.  Besides providing a convenient way to
introduce multiple record structures, this macro adds a theorem to the
theorems provided by that book: namely, that the accessor function
returns values of the right "type".

For example,

  (defun sbp16 (x)
    (declare (xargs :guard t))
    (and
     (integerp x)
     (<= (- (expt 2 15)) x)
     (< x (expt 2 15))))

  (defun fix-sbp16 (x)
    (declare (xargs :guard t))
    (if (sbp16 x) x 0))

  (defrecord sbp :rd getbv :wr putbv :fix fix-sbp16 :typep sbp16)

The "raw" record structure introduced in the standard records book is
used to define records defined using defrecord, and the functions for
accessing and updating a record that are introduced by defrecord are
proved to have many of the same properties as the records in the
standard records book.  In particular, assume that the record
introduced by defrecord has operations (g a r) and (s a v r) that get
and set elements of record r for address a and value v.  We prove the
following lemmas, each of which also holds of "raw" records:

(defthm g-same-s
  (equal (g a (s a v r))
         v))

(defthm g-diff-s
  (implies (not (equal a b))
           (equal (g a (s b v r))
                  (g a r))))

(defthm s-same-g
  (equal (s a (g a r) r)
         r))

(defthm s-same-s
  (equal (s a y (s a x r))
         (s a y r)))

(defthm s-diff-s
  (implies (not (equal a b))
           (equal (s b y (s a x r))
                  (s a x (s b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s)))))

In addition, the defrecord macro proves one additional lemma that is
not provable about raw records:

(defthm typep-g
  (typep (g a r)))

for a typep predicate provided by the user.

What makes this implementation of records interesting is that it has
the peculiar property that each of the lemmas has no "type"
hypotheses.  This makes reasoning about operations considerably
easier, but the implementation of the record operations is obscure, to
say the least.  We are interested in providing an implementation to
show that the theorems listed above are consistent.

(Historical Note: Matt Kaufmann of AMD proposed a challenge problem to
the ACL2 list in March, 2000 to define a "get" and "set" function
without hypotheses, based on a request of Rob Sumner's.  Kaufmann
released his version, which uses a bizarre record implementation to
avoid the type hypotheses.  (We posted our independantly-derived
solution to the challenge to the ACL2 list in Mar 2000, which uses a
strikingly similar approach.  Is there basically only one way to
implement these functions?)  An improved version that exploits the
total order of ACL2 objects was developed by Kaufmann and Sumners and
presented at the 2002 ACL2 workshop, and this book is incorporated
into the standard ACL2 books.  In 2002 we realized that we needed data
element type information - for example, that a memory returns only
bit-vectors - and wanted to continue to avoid unnecessary hypotheses.
This led us to create this enhancement.)

David Greve and Matt Wilding
November 2002

|#

(defun symbol-list-to-string (list)
  (declare (type (satisfies symbol-listp) list))
  (if (consp list)
      (concatenate 'string (symbol-name (car list)) (symbol-list-to-string (cdr list)))
    ""))

(defun symbol-list-to-string (list)
  (declare (type (satisfies symbol-listp) list))
  (if (consp list)
      (concatenate 'string (symbol-name (car list)) (symbol-list-to-string (cdr list)))
    ""))

(local (in-theory (enable alist::keys)))

(defund rkeys (r)
  (declare (type t r))
  (alist::keys (acl2->rcd r)))

(defthm in-key-set-s-aux-better
  (implies (not (ifrp r))  ;(wfr r)
           (equal (list::memberp a (alist::keys (s-aux p v r)))
                  (if v (or (equal a p)
                            (list::memberp a (alist::keys r)))
                    (and (not (equal a p))
                         (list::memberp a (alist::keys r))))))
  :hints (("goal" :in-theory (e/d (wfkeyed wfr s-aux) ()))))

(defthm rkeys-of-clr
  (list::setequiv (rkeys (clr key r))
                  (list::remove key (rkeys r)))
  :hints (("Goal" :in-theory (e/d (clr) (S==R)))))

;bzo make a t-p rule?
(defthm rkeys-iff
  (iff (rkeys r)
       r)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable RKEYS ACL2->RCD))))

(defthm rkeys-non-nil-tp
  (implies r
           (rkeys r))
  :rule-classes (:type-prescription))

;do we need all of these?

(defthm rkeys-when-not-consp
  (implies (not (consp r))
           (equal (RKEYS R)
                  (if (equal r nil)
                      nil
                    (list nil))))
  :hints (("Goal" :in-theory (enable rkeys ACL2->RCD))))

(defthm not-memberp-g-aux
  (implies
   (not (list::memberp a (alist::keys alist)))
   (equal (g-aux a alist) nil)))

(defthm non-memberp-g
  (implies
   (not (list::memberp a (rkeys r)))
   (not (g a r)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable rkeys g))))

(defthm memberp-g-aux
  (implies
   (and
    (rcdp alist)
    (list::memberp a (alist::keys alist)))
   (g-aux a alist)))

(defthm memberp-g
  (implies
   (list::memberp a (rkeys r))
   (g a r))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable rkeys g))))

(defthmd memberp-rkeys-reduction
  (iff (list::memberp a (rkeys r))
       (g a r)))

(defthm not-memberp-r
  (implies
   (not (list::memberp a (rkeys r)))
   (equal (clr a r) r))
  :hints (("Goal" :in-theory (e/d (clr memberp-rkeys-reduction) (s==r)))))

(defthm not-consp-rkeys-not-r
  (implies
   (not (consp (rkeys r)))
   (not r))
  :rule-classes (:forward-chaining))


(defthm wfkeyed-implies-not-nil-memberp
  (implies
   (wfkeyed tr)
   (not (list::memberp nil (alist::keys tr))))
  :hints (("Goal" :in-theory (enable wfkeyed alist::keys list::memberp))))

(defthm wfr-implies-not-nil-memberp
  (implies
   (wfr tr)
   (not (list::memberp nil (rkeys tr))))
  :hints (("Goal" :in-theory (enable rkeys wfr))))

;;
;; rkeyquiv
;;

(defun rkeysub (keys r1 r2)
  (if (consp keys)
      (let ((key (car keys)))
        (and (equal (g key r1) (g key r2))
             (rkeysub (remove (car keys) keys) (clr key r1) (clr key r2))))
    t))

(defthm rkeysub-id
  (rkeysub keys x x))

(defthm rkeysub-implies-equal
  (implies
   (and
    (rkeysub rkeys r1 r2)
    (subsetp (rkeys r1) rkeys)
    (subsetp (rkeys r2) rkeys))
   (iff (equal r1 r2) t)))

(defthm memberp-rkeysub-implication
  (implies
   (and
    (list::memberp a keys)
    (rkeysub keys r1 r2))
   (equal (g a r1) (g a r2)))
  :rule-classes (:forward-chaining))

(defthm memberp-rkeysub-implication-2
  (implies
   (and
    (list::memberp a keys)
    (not (equal (g a r1) (g a r2))))
   (not (rkeysub keys r1 r2)))
  :rule-classes (:forward-chaining))

(defthm rkeysub-setequiv-implication
  (implies
   (and
    (rkeysub (rkeys x) x y)
    (rkeysub (rkeys y) x y))
   (list::setequiv (rkeys x) (rkeys y)))
  :rule-classes (:forward-chaining))

(defun rkeysub-equiv-induction (s1 s2 x y)
  (if (consp s1)
      (let ((key (car s1)))
        (if (list::memberp key s2)
            (if (equal (g key x) (g key y))
                (rkeysub-equiv-induction (remove key s1) (remove key s2) (clr key x) (clr key y))
              nil)
          nil))
    (list s1 s2 x y)))

(defthm open-rkeysub-on-memberp
  (implies
   (list::memberp key keys)
   (equal (rkeysub keys r1 r2)
          (and (equal (g key r1) (g key r2))
               (rkeysub (remove key keys) (clr key r1) (clr key r2)))))
  :hints (("Goal" :expand ((RKEYSUB KEYS R1 R2) (LIST::MEMBERP KEY KEYS)))))

(defun rkeyquiv (x y)
  (and
   (rkeysub (rkeys x) x y)
   (rkeysub (rkeys y) x y)))

(defthm rkeyquiv-id
  (rkeyquiv x x))

(defthm rkeyquiv-implication
  (implies
   (rkeyquiv x y)
   (equal x y))
  :rule-classes (:forward-chaining))

(in-theory (disable rkeyquiv))

;; ==================================================================
;;
;; fixedpoint
;;
;; ==================================================================

(defund fixedpoint (r)
  (equal (g nil r) r))

;;
;; This is the local part of the definition of ifrp.  There
;; is a weaker condition on the record that guarantees that
;; (g nil x) decreases.
;;
(defund localfixedpoint (x)
  (or (not x)
      (not (rcdp x))
      (and (consp x)
           (null (cdr x))
           (consp (car x))
           (null (caar x)))))

(defthmd abstract-localfixedpoint
  (equal (localfixedpoint x)
         (subsetp (rkeys x) (list nil)))
  :hints (("Goal" :in-theory (enable
                              localfixedpoint
                              g
                              rkeys
                              acl2->rcd
                              alist::keys
                              ))))

;; This should leave you with expressions in terms of (len (rkeys x)),
;; boolean expressions over records, and expressions of the form (g
;; nil x).  I think that is a pretty nice result.  Now it's not so
;; bad to compute (fixedpoint (s a v r)) ..

;; AUX
(defthm leaf-measure-aux
  (implies
   (and
    (not (ifrp r))
    r)
   (< (acl2-count (g-aux a r)) (acl2-count r)))
  :rule-classes (:linear)
  :hints (("Goal" :induct (g-aux a r)
           :expand (ifrp r)
           :in-theory (enable g-aux rcdp ifrp))))

;; (rule-set records::aux leaf-measure-aux)

;; Transition
(local
(defthm leaf-measure-ifrp
  (implies
   (and
    (not (ifrp r))
    r)
   (< (acl2-count (g a r)) (acl2-count r)))
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable g ACL2->RCD)))))

;; AUX
(defthm g-aux-implies-inequality
  (implies
   (and
    (not (ifrp r))
    r)
   (not (equal (g-aux a r) r)))
  :hints (("Goal" :use leaf-measure-aux)))

;; Transition
(defthmd fixedpoint-to-ifrp
  (equal (fixedpoint r)
         (or (ifrp r) (not r)))
  :hints (("Goal" :in-theory (enable fixedpoint g ACL2->RCD)
           :cases ((null (g-aux nil r))))))

(defthmd abstract-fixedpoint-helper
  (equal (fixedpoint x)
         (if (null x) t
           (and (localfixedpoint x)
                (fixedpoint (g nil x)))))
  :rule-classes (:definition)
  :hints (("Goal" :in-theory (enable
                              localfixedpoint
                              FIXEDPOINT-TO-IFRP
                              ifrp
                              g
                              g-aux
                              acl2->rcd
                              ))))

(defthmd abstract-fixedpoint
  (equal (fixedpoint x)
         (if (null x) t
           (and (subsetp (rkeys x) (list nil))
                (fixedpoint (g nil x)))))
  :rule-classes (:definition)
  :hints (("Goal" :in-theory (enable abstract-fixedpoint-helper
                                     abstract-localfixedpoint))))

(defthmd fixedpoint-impact-on-keys
  (implies
   (fixedpoint r)
   (equal (rkeys r) (if r (list nil) nil)))
  :hints (("Goal" :in-theory (e/d (IFRP
                            ALIST::KEYS
                            fixedpoint-to-ifrp
                            rkeys
                            ACL2->RCD)))))

;; Export
(defthm fixedpoint-measure
  (implies
   (not (fixedpoint r))
   (< (acl2-count (g a r)) (acl2-count r)))
  :hints (("Goal" :in-theory (enable fixedpoint-to-ifrp)))
  :rule-classes (:linear))

;; Export
(defthm fixedpoint-nil
  (implies
   (not r)
   (fixedpoint r)))

;; Export
(defthm fixedpoint-implies-fixedpoint-gar
  (implies
   (fixedpoint r)
   (fixedpoint (g a r)))
  :hints (("Goal" :use fixedpoint-to-ifrp
           :in-theory (enable ACL2->RCD)
           :expand ((fixedpoint (g a r))
                    (g a r)))))

;; Export (?) .. Perhaps we would be better off casting (g a r)
;; as memberp?

(defthmd fixedpoint-gar-rewrite
  (implies
   (fixedpoint r)
   (equal (g a r) (if (null a) r nil)))
  :hints (("Goal" :in-theory (enable FIXEDPOINT-TO-IFRP ACL2->RCD)
           :expand ((g a r)))))

;;
;; This belongs in << library
;;
(defthm <<-converse
  (implies
   (and
    (NOT (<< X Y))
    (NOT (EQUAL X Y)))
   (<< Y X))
  :rule-classes (:forward-chaining))

;; AUX
(defun ifrp-s-aux (a v r)
  (if (endp r)
      (and (ifrp v) (not a))
    (if (null (cdr r))
        (if (<< a (caar r))
            (and (not v) (ifrp r))
          (and (null (caar r))
               (if (null a) (ifrp v)
                 (and (not v) (ifrp r)))))
      (if (<< a (caar r)) nil
        (if (equal a (caar r))
            (if v nil (ifrp (cdr r)))
          (and (ifrp (list (car r)))
               (let ((r (cdr r)))
                 (and (equal a (caar r))
                      (null v) (not (consp (cdr r)))))))))))

(defthm ifrp-s-aux-to-ifrp-s-aux
  (implies
   (rcdp r)
   (equal (ifrp (s-aux a v r))
          (ifrp-s-aux a v r)))
  :hints (("Goal"  :in-theory (enable s-aux)
           :do-not-induct t
           :expand ((RCDP (CDR R))
                    (s-aux a v r)
                    (s-aux a v (cdr r))))))

(defun ifrp-s-aux-member (a v r)
  (let ((keys (alist::keys r)))
    (let ((size (len keys)))
      (cond
       ((= 0 size) (and (not a) (ifrp v)))
       ((= 1 size) (and (list::memberp nil keys)
                        (if (<< a nil) (and (null v) (ifrp (g-aux nil r)))
                          (if (equal a nil) (and v (null a) (ifrp v))
                            (and (not v) (ifrp (g-aux nil r)))))))
       ((= 2 size) (and (ifrp (g-aux nil r))
                        (and a (list::memberp a keys) (not v))))
       (t nil)))))

(defthm ifrp-s-aux-reformulation
  (implies
   (rcdp r)
   (equal (ifrp-s-aux a v r)
          (ifrp-s-aux-member a v r)))
  :hints (("Goal" :do-not-induct t
           :expand ((alist::keys r)
                    (alist::keys (cdr r)))
           :in-theory (enable alist::keys
                              g-aux))))

(defun ifrp-s-member (a v r)
  (let ((keys (rkeys r)))
    (let ((size (len keys)))
      (cond
       ((= 0 size) (and (not a) (ifrp v)))
       ((= 1 size) (and (list::memberp nil keys)
                        (if (<< a nil) (and (null v) (ifrp (g nil r)))
                          (if (equal a nil) (and v (null a) (ifrp v))
                            (and (not v) (ifrp (g nil r)))))))
       ((= 2 size) (and (ifrp (g nil r))
                        (and a (list::memberp a keys) (not v))))
       (t nil)))))

(defun ifrp-s (a v r)
  (let ((keys (rkeys r)))
    (let ((size (len keys)))
      (cond
       ((= 0 size) (and (not a) (ifrp v)))
       ((= 1 size) (and (g nil r)
                        (if (<< a nil) (and (null v) (ifrp (g nil r)))
                          (if (equal a nil) (and v (null a) (ifrp v))
                            (and (not v) (ifrp (g nil r)))))))
       ((= 2 size) (and (ifrp (g nil r))
                        (and a (g a r) (not v))))
       (t nil)))))

(defthmd ifrp-s-to-ifrp-s-member
  (equal (ifrp-s a v r)
         (ifrp-s-member a v r))
  :hints (("Goal" :in-theory '(ifrp-s ifrp-s-member MEMBERP-RKEYS-REDUCTION))))

(defthm ifrp-rcd->acl2
  (implies
   (rcdp x)
   (equal (ifrp (rcd->acl2 x))
          (ifrp x)))
  :hints (("Goal" :in-theory (enable rcd->acl2))))

(defthm ifrp-s-to-ifrp-s
  (equal (ifrp (s a v r))
         (ifrp-s a v r))
  :hints (("Goal" :in-theory (e/d (ifrp-s-to-ifrp-s-member
                                   rkeys
                                   g s)
                                  (ifrp-s
                                   ifrp-s-aux)))))

(defthm consp-keys
  (equal (consp (alist::keys list))
         (consp list))
  :hints (("Goal" :in-theory (enable alist::keys))))

(defthm iff-s-aux-alt
  (implies
   (rcdp r)
   (iff (s-aux a v r)
        (not (or (and (not r)
                      (not V))
                 (and (equal (len (alist::keys r)) 1)
                      (list::memberp a (alist::keys r))
                      (not v))))))
  :hints (("Goal" :in-theory (enable alist::keys list::memberp))))

(defthm iff-rcd->acl2
  (implies
   (rcdp r)
   (iff (rcd->acl2 r)
        (if (ifrp r) (g nil r) r)))
  :hints (("Goal" :in-theory (enable ACL2->RCD rcd->acl2 g))))

(defthm g-aux-nil-ifrp
  (implies
   (ifrp r)
   (g-aux nil (acl2->rcd r)))
  :hints (("Goal" :in-theory (enable g-aux acl2->rcd))))

(defthm iff-acl2->rcd
  (iff (acl2->rcd r)
       (or (ifrp r) r))
  :hints (("Goal" :in-theory (enable acl2->rcd))))

(defun iff-s-member (a v r)
  (not (or (and (not (if (ifrp r) (g nil r) r))
                (not V))
           (and (equal (len (rkeys r)) 1)
                (list::memberp a (rkeys r))
                (not v)))))

(defun iff-s-ifrp (a v r)
  (not (or (and (not (if (ifrp r) (g nil r) r))
                (not V))
           (and (equal (len (rkeys r)) 1)
                (g a r)
                (not v)))))

(defthmd iff-s-ifrp-to-iff-s-member
  (equal (iff-s-ifrp a v r)
         (iff-s-member a v r))
  :hints (("Goal" :in-theory '(iff-s-ifrp iff-s-member MEMBERP-RKEYS-REDUCTION))))

(defthmd iff-s-to-iff-s-ifrp
  (iff (s a v r)
       (iff-s-ifrp a v r))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (iff-s-ifrp-to-iff-s-member rkeys g s)
                           (iff-s-ifrp)))))

;; It would be interesting if (fixedpoint (s a v r)) were amenible to
;; decomposition into an expression involving only fixedpoint

(defthmd ifrp-to-fixedpoint
  (equal (ifrp r) (if (not r) nil (fixedpoint r)))
  :hints (("Goal" :in-theory (enable FIXEDPOINT-TO-IFRP))))

(defun fixedpoint-s-fn (a v r)
  (or (let ((keys (rkeys r)))
        (let ((size (len keys)))
          (cond
           ((= 0 size) (and (not a) (ifrp-as-fixedpoint v)))
           ((= 1 size) (and (g nil r)
                            (if (<< a nil) (and (null v) (ifrp-as-fixedpoint (g nil r)))
                              (if (null a) (and v (ifrp-as-fixedpoint v))
                                (and (not v) (ifrp-as-fixedpoint (g nil r)))))))
           ((= 2 size) (and (ifrp-as-fixedpoint (g nil r))
                            (and a (g a r) (not v))))
           (t nil))))
      (and (not (if (ifrp-as-fixedpoint r) (g nil r) r))
           (not V))
      (and (equal (len (rkeys r)) 1)
           (g a r)
           (not v))))

;; This theorem allows us to describe fixedpoints relative to
;; (s a v r) in terms of:
;;
;; - iff r
;; - iff (g a r)
;; - iff v
;; - (len (rkeys r))
;; - (fixedpoint r)
;; - (fixedpoint v)
;;
(defthmd fixedpoint-s-to-fixedpoint-s-fn
  (equal (fixedpoint (s a v r))
         (fixedpoint-s-fn a v r))
  :hints (("Goal" :in-theory (enable iff-s-to-iff-s-ifrp
                                     FIXEDPOINT-TO-IFRP))))

(defun iff-s-fixedpoint (a v r)
  (not (or (and (not (if (ifrp-as-fixedpoint r) (g nil r) r))
                (not V))
           (and (equal (len (rkeys r)) 1)
                (g a r)
                (not v)))))

(defthmd iff-s-ifrp-to-iff-s-fixedpoint
  (equal (iff-s-ifrp a v r)
         (iff-s-fixedpoint a v r))
  :hints (("Goal" :in-theory (enable FIXEDPOINT-TO-IFRP))))

(defthmd iff-s-to-iff-s-fixedpoint
  (iff (s a v r)
       (iff-s-fixedpoint a v r))
  :hints (("Goal" :in-theory '(iff-s-to-iff-s-ifrp
                               iff-s-ifrp-to-iff-s-fixedpoint))))

(defthmd open-abstract-fixedpoint-on-s
  (implies
   (syntaxp (equal (car x) 's))
   (equal (fixedpoint x)
          (if (null x) t
            (and (subsetp (rkeys x) (list nil))
                 (fixedpoint (g nil x))))))
  :hints (("Goal" :in-theory (enable abstract-fixedpoint))))

;; ===================================================================
;;
;; These three theorems (possibly with abstract-fixedpoint) are
;; probably the ones you want for doing fixedpoint reasoning.
;;
;; ===================================================================

(defthmd gar-as-memberp
  (iff (g a r)
       (list::memberp a (rkeys r)))
  :hints (("Goal" :in-theory (enable memberp-rkeys-reduction))))

;; DAG - there is some concern about opening set functions into
;; "remove" .. I think that was what was causing problems below.
;; There should be a switch in the set library to turn this off.

(defthm iff-s
  (iff (s a v r)
       (or v
           (and r (if (acl2::fixedpoint r) a
                    (not (subsetp (rkeys r) (list a)))))))
  :hints (("Goal" :in-theory (e/d (iff-s-to-iff-s-fixedpoint
                                   gar-as-memberp
                                   fixedpoint-impact-on-keys)
                                  (LIST::MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP)))
          ("Subgoal 3''" :in-theory (enable list::memberp))))

(defthm fixedpoint-s
  (equal (fixedpoint (s a v r))
         (or
          ;; Results from (not (s a v r))
          (not (or v
                   (and r (if (acl2::fixedpoint r) a
                            (not (subsetp (rkeys r) (list a)))))))
          (and
           ;; Results from (localfixedpoint (s a v r))
           (if v (subsetp (cons a (rkeys r)) (list nil))
             (subsetp (rkeys r) (list a nil)))
           ;; Results from (fixedpoint (g nil (s a v r)))
           (if (null a) (fixedpoint v)
             (fixedpoint (g nil r))))))
  :hints (("Goal" :in-theory (e/d (rkeys-s
                                   g-of-s-redux
                                   iff-s
                                   abstract-localfixedpoint
                                   open-abstract-fixedpoint-on-s)
                                  ))))

(local (in-theory (disable SET::IN))) ;for efficiency
(local (in-theory (disable SET::SUBSET)))

(local (in-theory (disable mod floor))) ;bzo make non-local?

;bzo make a bunch of the stuff in this file local?

;; ((200 . 2) 1 . 3)

;; (defun cons-onto-all (item lst)
;;   (if (endp lst)
;;       nil
;;     (cons (cons item (car lst))
;;           (cons-onto-all item (cdr lst)))))

;bzo can we make this a set processor?
(defun cons-onto-all (item set)
  (if (set::empty set)
      (set::emptyset)
    (set::insert (cons item (set::head set))
                 (cons-onto-all item (set::tail set)))))

;bzo do we get this for a set processor?
(defthm cons-onto-all-iff
  (iff (cons-onto-all a set)
       (not (set::empty set))))


;if this didn't take a depth, how would we know to stop if an "element" of the tree happened to be another tree
(defund mem::domain-aux (mem-tree depth)
  (if (zp depth)
      (if mem-tree ;if it's not nil it's an element, so its location will become part of the domain
          (set::insert nil nil)
        nil)
    (if (not (consp mem-tree))
        (if mem-tree ;if it's not nil it's an element, so its location will become part of the domain
            (set::insert nil nil)
          nil)
      (set::union (cons-onto-all '0 (mem::domain-aux (car mem-tree) (+ -1 depth)))
                  (cons-onto-all '1 (mem::domain-aux (cdr mem-tree) (+ -1 depth)))))))


;this bits are in reverse order (least significant bit comes first in the list)
(defun convert-reversed-bit-list-to-integer (bit-list)
  (if (endp bit-list)
      0
    (+ (car bit-list)
       (* 2 (convert-reversed-bit-list-to-integer (cdr bit-list))))))

;; (defmacro def-set-processor (&key (processor-name 'unsupplied)
;;                                   (element-processor 'unsupplied)  ;can this be a term?
;;                                   (predicate 'unsupplied))
;;   `(defun ,processor-name (set) ;can this take more than one arg?
;;      (if (set::empty set)
;;          (set::emptyset)
;;        (if (,predicate (set::head set))
;;            (set::insert (,element-processor (set::head set))
;;                         (,processor-name (set::tail set)))
;;          (,processor-name (set::tail set))))))


;bzo use a set processor?
(defun convert-reversed-bit-lists-to-integers (bit-lists)
  (if (set::empty bit-lists)
      (set::emptyset)
    (set::insert (convert-reversed-bit-list-to-integer (set::head bit-lists))
                 (convert-reversed-bit-lists-to-integers (set::tail bit-lists)))))

(defthm convert-reversed-bit-lists-to-integers-iff
  (iff (convert-reversed-bit-lists-to-integers bit-lists)
       (not (set::empty bit-lists))))

(defthm convert-reversed-bit-lists-to-integers-of-insert
  (equal (convert-reversed-bit-lists-to-integers (set::insert lst lst-of-lsts))
         (set::insert (convert-reversed-bit-list-to-integer lst) (convert-reversed-bit-lists-to-integers lst-of-lsts)))
  :hints (("Goal" :use (:instance
                        (:functional-instance
                         goal-both-better
                         (generic-pred (lambda (a) t))
                         (process (lambda (a) (convert-reversed-bit-list-to-integer a)))
                         (process-set
                          (lambda (x) (convert-reversed-bit-lists-to-integers x))))
                        (a lst)
                        (x lst-of-lsts)

                        ))))

(defun mem::mem-tree-domain (mem-tree depth)
  (convert-reversed-bit-lists-to-integers (mem::domain-aux mem-tree depth)))

(defun natp-less-than-size (n size)
  (declare (xargs :guard t))
  (and (natp n)
       (< n (rfix size))))

(in-theory (disable SET::FILTER<NOT-NATP-LESS-THAN-SIZE>))

(defun mem::domain (mem)
  (let* ((mem-tree-part (caar mem))
         (record-part (cdddr mem))
         (depth (caddr mem))
         (size (cadr mem))
         )
    (set::union (SET::FILTER<NATP-LESS-THAN-SIZE> (mem::mem-tree-domain mem-tree-part depth) size)
                ;;Why can't we skip the filter above?  Doesn't mem-tree-domain
                ;;always return nats less than size?  Not necessarily.  There
                ;;may be nats less than 2^depth but greater than size.  We
                ;;have to filter them out.

                (SET::FILTER<not-NATP-LESS-THAN-SIZE> (set::rkeys record-part) size)
                )))

;dup in graph.lisp
;bzo rename
;; (defthm in-2list
;;   (equal (set::in a (list::2set list))
;;          (bag::memberp a list))
;;   :hints (("goal" :in-theory (enable set::2list bag::memberp)
;;            :induct (bag::memberp a list)
;;            )))

(defthm memory-p-means-not-_BAD-MEMORY-P
 (implies (mem::memory-p mem)
          (not (mem::|_BAD-MEMORY-P| mem)))
 :hints (("Goal" :expand ((MEM::|_BAD-MEMORY-P| MEM))
          :in-theory (enable mem::memory-p))))

(defthm _TO-MEM-does-nothing
 (implies (mem::memory-p mem)
          (equal (MEM::|_TO-MEM| mem)
                 mem))
 :hints (("Goal" :in-theory (enable MEM::|_TO-MEM|))))

(defthm _FROM-MEM-does-nothing
  (implies (mem::memory-p mem)
           (equal (MEM::|_FROM-MEM| mem)
                  mem))
  :hints (("Goal" :in-theory (enable MEM::|_FROM-MEM|))))

(defthm cons-onto-all-of-insert
  (equal (cons-onto-all item (set::insert lst lst-of-lsts))
         (set::insert (cons item lst) (cons-onto-all item lst-of-lsts)))
  :hints (("Goal" :use (:instance
                        (:functional-instance
                         goal-both-better
                         (generic-pred (lambda (a) t))
                         (process (lambda (a) (cons item a)))
                         (process-set
                          (lambda (x) (cons-onto-all item x))))
                        (a lst)
                        (x lst-of-lsts)

                        ))))

;bzo may ben expensive?
(defthm consp-iff-when-memtree
  (implies (and (MEM::|_MEMTREE-P| MEM-TREE DEPTH)
                (not (zp depth))
                )
           (iff (CONSP MEM-TREE)
                mem-tree))
  :hints (("Goal" :in-theory (enable MEM::|_MEMTREE-P|))))

(defthm _MEMTREE-P-of-cdr
  (implies (MEM::|_MEMTREE-P| MEM-TREE DEPTH)
           (MEM::|_MEMTREE-P| (CDR MEM-TREE)
                 (+ -1 DEPTH)))
  :hints (("Goal" :in-theory (enable MEM::|_MEMTREE-P|))))

(defthm _MEMTREE-P-of-car
  (implies (MEM::|_MEMTREE-P| MEM-TREE DEPTH)
           (MEM::|_MEMTREE-P| (CaR MEM-TREE)
                 (+ -1 DEPTH)))
  :hints (("Goal" :in-theory (enable MEM::|_MEMTREE-P|))))

(in-theory (disable SET::PICK-A-POINT-SUBSET-STRATEGY))

;bzo could declare CONS-ONTO-ALL to be a set processor (add such a facility to set-processor.lisp) and get this for free
(defthm cons-onto-all-of-singleton
  (equal (cons-onto-all item (list x))
         (list (cons item x)))
  :hints (("Goal" :in-theory (enable set::head
                                     set::empty
                                     set::tail)
           :expand ((set::setp (list x))
                    (set::insert (cons item x) nil)
                    (cons-onto-all item (list x))))))


;drop?
;bzo rename
(defthm helper34324324
 (implies (and (MEM::|_ADDRESS-P| ADDR DEPTH) ;(not (zp depth))
               elem)
          (EQUAL (MEM::DOMAIN-AUX (MEM::|_MEMTREE-STORE| ADDR ELEM NIL DEPTH) DEPTH)
                 (list (CONVERT-INTEGER-TO-REVERSED-BIT-LIST ADDR DEPTH))))
 :HINTS (("GOAL" :in-theory (enable mem::domain-aux
                                    MEM::|_MEMTREE-STORE|
                                    MEM::|_ADDRESS-P|
                                    MEM::|_MEMTREE-FIX|
;MEM::|_MEMTREE-P|
                                    MEM::|_ADDRESS-FIX|)
          :do-not '(generalize eliminate-destructors)
          :EXPAND ((MEM::|_MEMTREE-STORE| ADDR ELEM NIL DEPTH)))))





;bzo rename
(defthm helper285767657
  (implies (and elem
                (MEM::|_MEMTREE-P| MEM-TREE DEPTH)
                (MEM::|_ADDRESS-P| ADDR DEPTH))
           (equal (MEM::DOMAIN-AUX (MEM::|_MEMTREE-STORE| addr elem mem-tree depth) depth)
                  (set::insert (convert-integer-to-reversed-bit-list addr depth)
                               (MEM::DOMAIN-AUX mem-tree depth))
                  ))
  :otf-flg t
  :hints (("Subgoal *1/4'''" :expand ( ;(MEM::|_MEMTREE-STORE| (FLOOR ADDR 2)
    ;             ELEM NIL (+ -1 DEPTH))
    ;(MEM::|_MEMTREE-STORE| ADDR ELEM NIL DEPTH)
                                      ))
          ("Goal" :expand ((MEM::|_MEMTREE-STORE| (FLOOR ADDR 2)
                                 ELEM NIL (+ -1 DEPTH))
    ;(MEM::|_MEMTREE-STORE| ADDR ELEM NIL DEPTH)
                           (MEM::DOMAIN-AUX MEM-TREE depth))
           :do-not '(generalize eliminate-destructors)
           :induct t ;minor speedup
           :do-not-induct t
           :in-theory (e/d (mem::domain-aux
                              MEM::|_MEMTREE-STORE|
                              MEM::|_ADDRESS-P|
                              MEM::|_MEMTREE-FIX|
    ;MEM::|_MEMTREE-P|
                              MEM::|_ADDRESS-FIX|)
                           (;LIST::EQUAL-CONS-CASES ;bzo why?
                            )))))


(defthm _MEMTREE-STORE-iff
  (implies v
           (iff (MEM::|_MEMTREE-STORE| addr V mem-tree depth)
                t))
  :hints (("Goal" :in-theory (enable MEM::|_MEMTREE-STORE|))))

(defthm _MEMTREE-P-of-_MEMTREE-STORE-nil
  (implies (and (MEM::|_ADDRESS-P| A depth)
                v)
           (MEM::|_MEMTREE-P| (MEM::|_MEMTREE-STORE| A V nil depth) depth))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((MEM::|_MEMTREE-STORE| A V NIL DEPTH))
           :in-theory (enable MEM::|_MEMTREE-P|
                              MEM::|_MEMTREE-FIX|
                              MEM::|_ADDRESS-FIX|))))

(defthm _MEMTREE-P-of-_MEMTREE-STORE
  (implies (and (MEM::|_ADDRESS-P| A depth)
                (MEM::|_MEMTREE-P| memtree depth)
                v)
           (MEM::|_MEMTREE-P| (MEM::|_MEMTREE-STORE| A V memtree depth) depth))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((MEM::|_MEMTREE-STORE| A V MEMTREE DEPTH)
                    (MEM::|_MEMTREE-STORE| A V NIL DEPTH))
           :in-theory (enable MEM::|_MEMTREE-P|
                              MEM::|_MEMTREE-FIX|
                              MEM::|_ADDRESS-FIX|))))



(defthm CONVERT-REVERSED-BIT-LIST-TO-INTEGER-of-CONVERT-INTEGER-TO-REVERSED-BIT-LIST
  (implies (and (natp a)
                (< a (expt 2 len))
                (natp len))
           (EQUAL (CONVERT-REVERSED-BIT-LIST-TO-INTEGER
                   (CONVERT-INTEGER-TO-REVERSED-BIT-LIST A len))
                  A))
  )

(defund good-memoryp (mem)
  (and (mem::memory-p mem)
;       (wfr (cdddr mem))
       (set::all<natp-less-than-size> (mem::mem-tree-domain (caar mem) (caddr mem)) (cadr mem))
       (set::all<not-natp-less-than-size> (set::rkeys (cdddr mem)) (cadr mem))

       (equal (signed-byte-p 30 (caddr mem))
              (cdar mem))

;bzo drop?
       (if (equal 1 (cadr mem)) ;log2 on 0 is weird, so we handle this case specially
           (equal 1 (caddr mem))
         (equal (mem::|_LOG2| (+ -1 (cadr mem)))
                (caddr mem)))))


;bzo the macro should do this...
(defthm FILTER<NOT-NATP-LESS-THAN-SIZE>-of-insert
  (equal (SET::FILTER<NOT-NATP-LESS-THAN-SIZE> (set::insert a x) size)
         (if (not (and (natp a)
                       (< a (rfix size))))
             (set::insert a (SET::FILTER<NOT-NATP-LESS-THAN-SIZE> x size))
           (SET::FILTER<NOT-NATP-LESS-THAN-SIZE> x size)))
  :otf-flg t
  :hints (("Goal" :in-theory (enable SET::FILTER<NOT-NATP-LESS-THAN-SIZE>)
           :use (:instance
                 (:functional-instance
                  goal-both-better
                  (generic-pred (lambda (a)  (not (and (natp a)
                                                       (< a (rfix size))))))
                  (process (lambda (a) a))
                  (process-set
                   (lambda (x) (SET::FILTER<NOT-NATP-LESS-THAN-SIZE> x size))))
                 (a a)
                 (x x)

                 ))))

(defthm FILTER<NATP-LESS-THAN-SIZE>-of-insert
  (equal (SET::FILTER<NATP-LESS-THAN-SIZE> (set::insert a x) size)
         (if (and (natp a)
                       (< a (rfix size)))
             (set::insert a (SET::FILTER<NATP-LESS-THAN-SIZE> x size))
           (SET::FILTER<NATP-LESS-THAN-SIZE> x size)))
  :otf-flg t
  :hints (("Goal" :use (:instance
                        (:functional-instance
                         goal-both-better
                         (generic-pred (lambda (a)  (and (natp a)
                                                              (< a (rfix size)))))
                         (process (lambda (a) a))
                         (process-set
                          (lambda (x) (SET::FILTER<NATP-LESS-THAN-SIZE> x size))))
                        (a a)
                        (x x)

                        ))))

(defthm domain-of-store-v-non-nil
  (implies (and ;(MEM::MEMORY-P mem)
;(WFR (CDDDR MEM))
            (good-memoryp mem)
            v ;is not nil (maybe that's all we need?)
            )
           (equal (mem::domain (mem::store a v mem))
                  (set::insert a (mem::domain mem))))
  :otf-flg t
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (good-memoryp
                              MEM::|_ADDRESS-P|
                              MEM::SIZE
                              MEM::STORE MEM::|_STORE|
                              MEM::|_FROM-MEM|
                              MEM::|_BAD-MEMORY-P|
                              MEM::|_MEMORY-P|
                              MEM::|_MEMORY-MTREE|
                              MEM::|_MEMORY-FIX|
                              MEM::MEMORY-P
                              MEM::|_MEMORY-DEPTH|
                              MEM::|_MEMORY-FAST|
                              MEM::|_MEMORY-SIZE|
                              MEM::|_MEMORY-RECORD|

                              )
                           (SET::DOUBLE-CONTAINMENT
                            )))))

;show how s affects this...

;for typed records gotta unwrap the domain...

(in-theory (disable mem::domain)) ;move back

;bzo add to sets library
(defthm delete-of-insert-diff
  (implies (not (equal a b))
           (equal (set::delete a (set::insert b x))
                  (set::insert b (set::delete a x))))
  :hints (("Goal" :in-theory (enable SET::PICK-A-POINT-SUBSET-STRATEGY)
           :do-not '(generalize eliminate-destructors))))

(defthm not-in-cons-and-cons-onto-all
  (implies (not (set::in x y))
           (not (set::in (cons a x)
                         (cons-onto-all a y)))))

(defthm sfix-does-nothing-rewrite
  (equal (EQUAL (SET::SFIX x) x)
         (set::setp x)))

(defthm setp-of-cons-onto-all
  (set::setp (cons-onto-all a x)))

(defthm delete-of-cons-onto-all
  (equal (set::delete (cons a x)
                      (cons-onto-all a y))
         (cons-onto-all a (set::delete x y)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm not-in-cons-and-cons-onto-all-2
  (implies (not (equal a b))
           (not (set::in (cons a x)
                         (cons-onto-all b y)))))

(local (in-theory (disable SET::UNION-DELETE-Y)))
(local (in-theory (disable SET::UNION-DELETE-x)))

(defthm delete-of-union-irrel-1
 (implies (not (set::in a x))
          (equal (set::delete a (set::union x y))
                 (set::union x (set::delete a y))))
 :hints (("Goal" :in-theory (enable SET::UNION-DELETE-Y))))

(defthm delete-of-union-irrel-2
  (implies (not (set::in a y))
           (equal (set::delete a (set::union x y))
                  (set::union y (set::delete a x))))
  :hints (("Goal" :in-theory (enable SET::UNION-DELETE-x))))

(defthm helper285767657-nil-version
  (implies (and (MEM::|_MEMTREE-P| MEM-TREE DEPTH)
                (MEM::|_ADDRESS-P| ADDR DEPTH))
           (equal (MEM::DOMAIN-AUX (MEM::|_MEMTREE-STORE-NIL| addr mem-tree depth) depth)
                  (set::delete (convert-integer-to-reversed-bit-list addr depth)
                               (MEM::DOMAIN-AUX mem-tree depth))
                  ))
  :otf-flg t
  :hints (
          ("Goal" :expand (
    ;(MEM::|_MEMTREE-STORE| ADDR ELEM NIL DEPTH)
                           (MEM::DOMAIN-AUX MEM-TREE depth))
           :do-not '(generalize eliminate-destructors)
           :induct t ;minor speedup
           :do-not-induct t
           :in-theory (enable MEM::DOMAIN-AUX
                              MEM::|_MEMTREE-STORE-NIL|
                              MEM::|_ADDRESS-P|
                              MEM::|_MEMTREE-FIX|
    ;MEM::|_MEMTREE-P|
                              MEM::|_ADDRESS-FIX|))))


(in-theory (disable delete-of-union-irrel-1
                    delete-of-union-irrel-2))

(in-theory (enable SET::UNION-DELETE-x
                   SET::UNION-DELETE-y))

(defthm subset-delete-self
  (equal (set::subset x (set::delete a x))
         (not (set::in a x))))

;; (defun all-have-len (len x)
;;   (if (set::empty x)
;;       t
;;     (and (equal len (len (set::head x)))
;;          (all-have-len len (set::tail x)))))

(defun len-equal (a len)
  (declare (xargs :guard t))
  (equal (len a) (rfix len)))

(defthm all-len-equal-of-union
  (equal (set::all<len-equal> (set::union x y) depth)
         (and (set::all<len-equal> x depth)
              (set::all<len-equal> y depth))))

(defthm all-len-equal-of-cons-onto-all
  (implies (not (zp depth))
           (equal (SET::ALL<LEN-EQUAL> (CONS-ONTO-ALL a x) DEPTH)
                  (SET::ALL<LEN-EQUAL> x (+ -1 DEPTH)))))

(defthm all-len-equal-of-domain-aux
  (implies (and (natp depth)
                (mem::_memtree-p tree depth))
           (set::all<len-equal> (MEM::DOMAIN-AUX tree depth) depth))
  :hints (("Goal" :in-theory (enable MEM::DOMAIN-AUX)
           :do-not '(generalize eliminate-destructors))))

;bzo dup?
(DEFUN BITP (B)
  "Documentation available via :doc"
  (DECLARE (XARGS :GUARD T))
  (OR (EQUAL B 0) (EQUAL B 1)))

(defun bit-listp (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (and (bitp (car lst))
           (bit-listp (cdr lst)))
    t))

(defthm integerp-of-CONVERT-REVERSED-BIT-LIST-TO-INTEGER
  (implies (bit-listp rbl)
           (natp (CONVERT-REVERSED-BIT-LIST-TO-INTEGER rbl)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable CONVERT-REVERSED-BIT-LIST-TO-INTEGER))))

;nested inductions
;kill the other
(defthm convert-reversed-bit-list-to-integer-of-convert-integer-to-reversed-bit-list-2
 (implies (and (force (natp n))
               (force (< n (expt 2 len)))
               )
          (equal (convert-reversed-bit-list-to-integer (convert-integer-to-reversed-bit-list n len))
                 n)))

(in-theory (disable SET::ALL<BIT-LISTP>))
(in-theory (disable SET::ALL<not-BIT-LISTP>))
(in-theory (disable SET::ALL-IN-2-NOT<BIT-LISTP>))

;(in-theory (disable SET::FILTER-IN-NOT<NATP-LESS-THAN-SIZE>))

(in-theory (disable SET::ALL<NOT-TRUE-LISTP>))
(in-theory (disable SET::ALL<TRUE-LISTP>))
(in-theory (disable SET::ALL-IN-2-NOT<TRUE-LISTP>))
(in-theory (disable SET::ALL-IN-2<TRUE-LISTP>))

(defthm len-of-CONVERT-INTEGER-TO-REVERSED-BIT-LIST
  (equal (LEN (CONVERT-INTEGER-TO-REVERSED-BIT-LIST A len))
         (nfix len)))

(defthm convert-integer-to-reversed-bit-list-equal-rewrite
  (implies (and (true-listp x)
                (bit-listp x)
                (natp a)
                (< a (expt 2 (len x)))
                )
           (equal (equal (convert-integer-to-reversed-bit-list a (len x)) x)
                  (equal a (convert-reversed-bit-list-to-integer x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm in-of-convert-reversed-bit-lists-to-integers
  (implies (and (force (set::all<len-equal> bit-lists len))
                (force (set::all<bit-listp> bit-lists))
                (force (set::all<true-listp> bit-lists))
                (force (natp a))
                (force (< a (expt 2 len)))
                (not (zp len)))
           (equal (set::in a (convert-reversed-bit-lists-to-integers bit-lists))
                  (set::in (convert-integer-to-reversed-bit-list a len) bit-lists)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm not-in-of-convert-reversed-bit-lists-to-integers
  (implies (and (not (natp a))
                (force (set::all<bit-listp> bit-lists)))
           (not (set::in a (convert-reversed-bit-lists-to-integers bit-lists))))
  :hints (("Goal" :in-theory (enable SET::ALL<BIT-LISTP>
                                     )
           :do-not '(generalize eliminate-destructors))))

;(local (in-theory (disable LIST::EQUAL-OF-BOOLEANS-REWRITE)))
(local (in-theory (disable acl2::equal-booleans-reducton)))

(defthm in-of-convert-reversed-bit-lists-to-integers-better
  (implies (and (force (set::all<len-equal> bit-lists len))
                (force (set::all<bit-listp> bit-lists))
                (force (set::all<true-listp> bit-lists))
;                (force (natp a))
                (force (< a (expt 2 len)))
                (not (zp len)))
           (equal (set::in a (convert-reversed-bit-lists-to-integers bit-lists))
                  (and (natp a)
                       (set::in (convert-integer-to-reversed-bit-list a len) bit-lists))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm in-of-convert-reversed-bit-lists-to-integers-better2
  (implies (and (force (set::all<len-equal> bit-lists (len (set::head bit-lists))))
                (force (set::all<bit-listp> bit-lists))
                (force (set::all<true-listp> bit-lists))
;                (force (natp a))
                (force (< a (expt 2 (len (set::head bit-lists)))))
                (not (zp (len (set::head bit-lists)))))
           (equal (set::in a (convert-reversed-bit-lists-to-integers bit-lists))
                  (and (natp a)
                       (set::in (convert-integer-to-reversed-bit-list a (len (set::head bit-lists))) bit-lists))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;need to know the extra fact that the record doesn't have any usb32s (or whatevers) among its keys
;perhaps remove the usb32s from the rkeys of the record?

;show the stronger version of good-memoryp is preserved by stores?

;; (defthm consp-len-hack
;;   (implies (< 0 (len x)) (consp x)))

;bzo should the quantify macro generate this too?
(defthm delete-of-filter<not-natp-less-than-size>
  (equal (set::delete a (set::filter<not-natp-less-than-size> set size))
         (if (not (and (natp a)
                       (< a (rfix size))))
             (set::filter<not-natp-less-than-size> (set::delete a set) size)
           (set::filter<not-natp-less-than-size> set size)))
  :hints (("Goal" :in-theory (enable SET::FILTER<NOT-NATP-LESS-THAN-SIZE>))))

(defthm delete-of-filter<natp-less-than-size>
  (equal (set::delete a (set::filter<natp-less-than-size> set size))
         (if (and (natp a)
                  (< a (rfix size)))
             (set::filter<natp-less-than-size> (set::delete a set) size)
           (set::filter<natp-less-than-size> set size))))

(defthm setp-of-convert-reversed-bit-lists-to-integers
  (set::setp (convert-reversed-bit-lists-to-integers bit-lists)))

(local
 (defun double-cdr-induct (x y)
   (if (endp x)
       (list x y)
     (double-cdr-induct (cdr x) (cdr y)))))

(defthm two-calls-to-CONVERT-REVERSED-BIT-LIST-TO-INTEGER-must-differ
  (implies (and (not (equal a b))
                (bit-listp a)
                (bit-listp b)
                (true-listp a)
                (true-listp b)
                (equal (len a) (len b)))
           (NOT (EQUAL (CONVERT-REVERSED-BIT-LIST-TO-INTEGER A)
                       (CONVERT-REVERSED-BIT-LIST-TO-INTEGER b))))
  :hints (("Goal" :induct (double-cdr-induct a b)
           :do-not '(generalize eliminate-destructors))))

(defthm not-in-CONVERT-REVERSED-BIT-LIST-TO-INTEGER-CONVERT-REVERSED-BIT-LIST-TO-INTEGERs
  (IMPLIES
   (AND (not (set::in a x))
        (SET::ALL<LEN-EQUAL> x len)
        (SET::ALL<TRUE-LISTP> x)
    ;       (BIT-LISTP (SET::HEAD x))
        (SET::ALL<BIT-LISTP> x)
        (natp len)
        (bit-listp a)
        (true-listp a)
        (equal (len a) len)
        )
   (NOT
    (SET::IN (CONVERT-REVERSED-BIT-LIST-TO-INTEGER a)
             (CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS x))))
  :hints (("Goal" :in-theory (enable set::in
                                     )
           :do-not '(generalize eliminate-destructors))))

(defthm not-in-CONVERT-REVERSED-BIT-LIST-TO-INTEGER-CONVERT-REVERSED-BIT-LIST-TO-INTEGERs-better
  (IMPLIES
   (AND (not (set::in a x))
        (SET::ALL<LEN-EQUAL> x (len (set::head x)))
        (SET::ALL<TRUE-LISTP> x)
    ;       (BIT-LISTP (SET::HEAD x))
        (SET::ALL<BIT-LISTP> x)
        (natp (len (set::head x)))
        (bit-listp a)
        (true-listp a)
        (equal (len a) (len (set::head x)))
        )
   (NOT
    (SET::IN (CONVERT-REVERSED-BIT-LIST-TO-INTEGER a)
             (CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm use-all-len-equal
  (implies (and (set::all<len-equal> x len)
                (rationalp len)
                )
           (equal (len (set::head x))
                  (if (not (set::empty x))
                      len
                  0)))
  :hints (("Goal" :expand ((set::all<len-equal> x len)))))

(defthm true-listp-of-head
 (implies (set::all<true-listp> lists)
          (true-listp (set::head lists)))
 :hints (("Goal" :in-theory (enable set::all<true-listp>))))

(defthm delete-of-CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS
  (implies (and (set::all<len-equal> bit-lists len)
                (SET::ALL<TRUE-LISTP> BIT-LISTS)
                (SET::ALL<bit-LISTP> BIT-LISTS)
                (natp a)
                (rationalp len)
    ;               (< a len)
                (natp len)
                (< A (EXPT 2 len))
                )
           (equal (SET::DELETE A (CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS bit-lists))
                  (CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS
                   (SET::DELETE (CONVERT-INTEGER-TO-REVERSED-BIT-LIST A len)
                                bit-lists))))
  :hints (("Subgoal *1/2" :cases ((SET::EMPTY (SET::TAIL BIT-LISTS))))
          ("Goal" :in-theory (disable ;test
                              (:type-prescription CONVERT-INTEGER-TO-REVERSED-BIT-LIST) ;had to disable this
                              )
           :do-not '(generalize eliminate-destructors))))

(defthm delete-of-CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS2
  (implies (and (set::all<len-equal> bit-lists (len (set::head bit-lists)))
                (SET::ALL<TRUE-LISTP> BIT-LISTS)
                (SET::ALL<bit-LISTP> BIT-LISTS)
                (natp a)
                (rationalp (len (set::head bit-lists)))
    ;               (< a len)
                (natp (len (set::head bit-lists)))
                (< A (EXPT 2 (len (set::head bit-lists))))
                )
           (equal (SET::DELETE A (CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS bit-lists))
                  (CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS
                   (SET::DELETE (CONVERT-INTEGER-TO-REVERSED-BIT-LIST
                                 A (len (set::head bit-lists)))
                                bit-lists))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm len-of-head-of-domain-aux
  (implies (and (natp depth)
                (mem::_memtree-p mem depth))
           (equal (len (set::head (mem::domain-aux mem depth)))
                  (if (set::empty (mem::domain-aux mem depth))
                      0
                    (nfix depth))))
  :hints (("Goal" :use (:instance all-len-equal-of-domain-aux (tree mem))
           :in-theory (disable mem::domain-aux all-len-equal-of-domain-aux MEM::|_MEMTREE-P|)
           :do-not '(generalize eliminate-destructors))))

(defthm all-true-listp-of-DOMAIN-AUX
  (SET::ALL<TRUE-LISTP> (MEM::DOMAIN-AUX tree depth))
  :hints (("Goal" :in-theory (enable MEM::DOMAIN-AUX SET::ALL<TRUE-LISTP>))))

;bzo - is this a general theorem that quantify should give us?
;the need for it arose when i disabled SET::ALL<BIT-LISTP>, since the definition rule was high on accumulated persistence
(defthm not-all-BIT-LISTP-when-not-head
  (IMPLIES (AND (NOT (BIT-LISTP (SET::HEAD SET::SET-FOR-ALL-REDUCTION)))
                (NOT (SET::EMPTY SET::SET-FOR-ALL-REDUCTION)))
           (NOT (SET::ALL<BIT-LISTP> SET::SET-FOR-ALL-REDUCTION)))
  :hints (("Goal" :in-theory (enable SET::ALL<BIT-LISTP>))))

(defthm all-bit-listp-of-domain-aux
  (set::all<bit-listp> (mem::domain-aux tree depth))
    :hints (("Goal" :in-theory (enable mem::domain-aux acl2::equal-booleans-reducton))))
;; LIST::EQUAL-OF-BOOLEANS-REWRITE

(defthm setp-of-domain-aux
  (set::setp (mem::domain-aux tree depth))
  :hints (("Goal" :in-theory (enable MEM::DOMAIN-AUX))))

;should this be generated by the filter macro?
(defthm use-all<not-natp-less-than-size>
  (implies (and (set::all<not-natp-less-than-size> x sz)
                (natp-less-than-size a sz)
                (set::setp x)
                )
           (equal (set::delete a x)
                  x)))

(defthm use-all<natp-less-than-size>
  (implies (and (set::all<natp-less-than-size> x sz)
                (not (natp-less-than-size a sz))
                (set::setp x)
                )
           (equal (set::delete a x)
                  x)))

;auto-generate this?
(defthm convert-reversed-bit-lists-to-integers-of-delete-subset
  (set::subset (convert-reversed-bit-lists-to-integers (set::delete bl bls))
               (convert-reversed-bit-lists-to-integers bls)))

(local
 (defthm 2set-remove
   (equal (list::2set (list::remove a list))
          (set::delete a (list::2set list))))
 )

(local (in-theory (disable set::delete-2set)))

;bzo now combine the cases..
(defthm domain-of-store-v-nil
  (implies (and (good-memoryp mem)
                (not v)
                )
           (equal (mem::domain (mem::store a v mem))
                  (set::delete a (mem::domain mem))))
  :otf-flg t
  :hints (("Goal" :do-not-induct t
           :cases ((SET::EMPTY (MEM::DOMAIN-AUX (CAR (CAR MEM))
                                                (CAR (CDR (CDR MEM))))))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (set::delete-of-union-push-into-both

                            good-memoryp
                            MEM::DOMAIN
                            MEM::|_ADDRESS-P|
                            MEM::SIZE
                            MEM::STORE MEM::|_STORE|
                            MEM::|_FROM-MEM|
                            MEM::|_BAD-MEMORY-P|
                            MEM::|_MEMORY-P|
                            MEM::|_MEMORY-MTREE|
                            MEM::|_MEMORY-FIX|
                            MEM::MEMORY-P
                            MEM::|_MEMORY-DEPTH|
                            MEM::|_MEMORY-FAST|
                            MEM::|_MEMORY-SIZE|
                            MEM::|_MEMORY-RECORD|
                            )
                           (SET::DOUBLE-CONTAINMENT
                            SET::UNION-DELETE-y
                            SET::UNION-DELETE-x)))))

(defthm domain-of-store
  (implies (good-memoryp mem)
           (equal (mem::domain (mem::store a v mem))
                  (if v
                      (set::insert a (mem::domain mem))
                    (set::delete a (mem::domain mem))))))

;bzo  make DOMAIN-OF-STORE-V-NON-NIL etc. local

(in-theory (disable DOMAIN-OF-STORE-V-NON-NIL DOMAIN-OF-STORE-V-nil))

;prove setp of domain
(defthm setp-of-domain
  (set::setp (mem::domain mem))
  :hints (("Goal" :in-theory (enable mem::domain))))

;bzo move!
(defthm domain-of-new
  (equal (mem::domain (mem::new size))
         nil)
  :hints (("Goal" :in-theory (enable MEM::DOMAIN-AUX
                                     mem::new
                                     mem::domain
                                     mem::mem-tree-domain))))

(defthm mem::mem-tree-domain-of-nil
  (equal (mem::mem-tree-domain nil depth)
         nil)
  :hints (("Goal" :in-theory (enable MEM::DOMAIN-AUX
                                     mem::mem-tree-domain
                                     ))))

(defthm natp-of-_LOG2
  (natp (MEM::|_LOG2| n))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable MEM::|_LOG2|))))

(defthm _memtree-p-of-nil
  (mem::|_MEMTREE-P| nil depth)
  :hints (("Goal" :in-theory (enable MEM::|_MEMTREE-P|))))

(defthm log2-equal-0-rewrite
  (implies (natp size)
           (equal (EQUAL (MEM::|_LOG2| size) 0)
                  (equal 0 size)))
  :hints (("Goal" :expand ((MEM::|_LOG2| SIZE)))))

(defthm good-memoryp-of-new
  (implies (posp size)
           (good-memoryp (mem::new size)))
  :otf-flg t
  :hints (("Goal" :in-theory (enable mem::new
                                     good-memoryp
                                     MEM::|_MEMORY-DEPTH|
                                     MEM::|_MEMORY-FIX|
                                     MEM::|_MEMORY-SIZE|
                                     MEM::|_MEMORY-P|
                                     MEM::MEMORY-P
                                     ))))
;bzo provide a macro for disabling a function's executable counterpart but allowing it to run on small values?
;(local (in-theory (disable (:executable-counterpart expt))))

;; (local
;;  (defthm good-memoryp-of-store-1
;;    (implies (and (good-memoryp mem)
;;                  a)
;;             (wfr (cdddr (mem::store a v mem) )))
;;    :otf-flg t
;;    :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;             :cases (a)
;;             :in-theory (enable WFKEY
;;                                MEM::MEMORY-P
;;                                MEM::|_MEMORY-FAST|
;;                                MEM::|_MEMORY-SIZE|
;;                                MEM::|_MEMORY-DEPTH|
;;                                MEM::|_MEMORY-P|
;;                                MEM::|_BAD-MEMORY-P|
;;                                MEM::|_MEMORY-MTREE|
;;                                MEM::STORE
;;                                MEM::|_TO-MEM|
;;                                MEM::|_STORE|
;;                                MEM::|_FROM-MEM|
;;                                GOOD-MEMORYP
;;                                MEM::|_MEMORY-RECORD|
;;                                MEM::|_MEMORY-FIX|
;;                                )))))


(local
 (defthm rkeys-of-cdddr-of-store
   (implies (good-memoryp mem)
            (equal (SET::RKEYS (CDDDR (MEM::STORE A V MEM)))
                   (if (not (natp-less-than-size a (CADR MEM)))
                       (if v
                           (set::insert a (set::rkeys (CDDDR MEM)))
                         (set::delete a (set::rkeys (CDDDR MEM))))
                     (SET::RKEYS (CDDDR MEM)))))
   :otf-flg t
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable MEM::STORE
                               MEM::MEMORY-P
                               MEM::SIZE
                               MEM::|_ADDRESS-P|
                               MEM::|_MEMORY-P|
                               MEM::|_MEMORY-SIZE|
                               MEM::|_MEMORY-DEPTH|
                               MEM::|_MEMORY-FAST|
                               MEM::|_TO-MEM|
                               MEM::|_FROM-MEM|
                               MEM::|_STORE|
                               MEM::|_MEMORY-MTREE|
                               MEM::|_MEMORY-FIX|
                               GOOD-MEMORYP
                               MEM::|_MEMORY-RECORD|
                               )))))

(local
 (defthm cadr-of-_store
   (implies (good-memoryp mem)
            (equal (CADR (MEM::_STORE A V MEM))
                   (CADR MEM)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable ;MEM::STORE
;MEM::|_FROM-MEM|
;MEM::|_TO-MEM|
                        MEM::|_STORE|
                        GOOD-MEMORYP
                        MEM::MEMORY-P
;MEM::|_MEMORY-P|
                        MEM::|_MEMORY-SIZE|
                        MEM::|_MEMORY-FIX|
                        )))))

(local
 (defthm cdar-of-_store
   (implies (good-memoryp mem)
            (equal (CDaR (MEM::_STORE A V MEM))
                   (CDaR MEM)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable MEM::|_MEMORY-FAST|
;MEM::STORE
;MEM::|_FROM-MEM|
;MEM::|_TO-MEM|
                               MEM::|_STORE|
                               GOOD-MEMORYP
                               MEM::MEMORY-P
;MEM::|_MEMORY-P|
                               MEM::|_MEMORY-SIZE|
                               MEM::|_MEMORY-FIX|
                               )))))

(local
 (defthm caddr-of-_store
   (implies (good-memoryp mem)
            (equal (CAdDR (MEM::_STORE A V MEM))
                   (CAdDR MEM)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable ;MEM::STORE
;MEM::|_FROM-MEM|
;MEM::|_TO-MEM|
                        MEM::|_STORE|
                        GOOD-MEMORYP
                        MEM::MEMORY-P
;MEM::|_MEMORY-P|
                        MEM::|_MEMORY-SIZE|
                        MEM::|_MEMORY-FIX|
                        MEM::|_MEMORY-DEPTH|
                        )))))

(local
 (defthm cadr-of-store
   (implies (good-memoryp mem)
            (equal (CADR (MEM::STORE A V MEM))
                   (CADR MEM)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable MEM::STORE
                               MEM::|_FROM-MEM|
                               MEM::|_TO-MEM|
;                             MEM::|_STORE|
                               GOOD-MEMORYP
                               MEM::MEMORY-P
                               MEM::|_MEMORY-P|
                               )))))

(local
 (defthm cdar-of-store
   (implies (good-memoryp mem)
            (equal (CDaR (MEM::STORE A V MEM))
                   (CDaR MEM)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable MEM::STORE
                               MEM::|_FROM-MEM|
                               MEM::|_TO-MEM|
;                             MEM::|_STORE|
                               GOOD-MEMORYP
                               MEM::MEMORY-P
                               MEM::|_MEMORY-P|
                               )))))

(local
 (defthm caddr-of-store
   (implies (good-memoryp mem)
            (equal (CADdR (MEM::STORE A V MEM))
                   (CADdR MEM)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable MEM::STORE
                               MEM::|_FROM-MEM|
                               MEM::|_TO-MEM|
;                             MEM::|_STORE|
                               GOOD-MEMORYP
                               MEM::MEMORY-P
                               MEM::|_MEMORY-P|
                               )))))

(in-theory (disable MEM::MEM-TREE-DOMAIN))

(defthm mem-tree-domain-after-store
  (implies (good-memoryp mem)
           (equal (MEM::MEM-TREE-DOMAIN (CAAR (MEM::STORE A V MEM))
                                        (CADDR ;(MEM::STORE A V
                                         MEM
                                         ;)
                                         ))
                  (if (natp-less-than-size a (CADR MEM))
                      (if v
                          (set::insert a (MEM::MEM-TREE-DOMAIN (CAAR MEM)
                                                               (CADDR MEM)))
                        (set::delete a (MEM::MEM-TREE-DOMAIN (CAAR MEM)
                                                             (CADDR MEM))))
                    (MEM::MEM-TREE-DOMAIN (CAAR MEM)
                                          (CADDR MEM)))))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;           :use (:instance domain-of-store) ;gross way to prove this...
           :cases ((SET::EMPTY (MEM::DOMAIN-AUX (CAR (CAR MEM))
                                                      (CAR (CDR (CDR MEM))))))

           :in-theory (e/d (MEM::DOMAIN

                            MEM::MEM-TREE-DOMAIN
                            MEM::STORE
                            MEM::MEMORY-P
                            MEM::SIZE
                            MEM::|_ADDRESS-P|
                            MEM::|_MEMORY-P|
                            MEM::|_MEMORY-SIZE|
                            MEM::|_MEMORY-DEPTH|
                            MEM::|_MEMORY-FAST|
                            MEM::|_TO-MEM|
                            MEM::|_FROM-MEM|
                            MEM::|_STORE|
                            MEM::|_MEMORY-MTREE|
                            MEM::|_MEMORY-FIX|
                            GOOD-MEMORYP
                            MEM::|_MEMORY-RECORD|
                            )
                           (domain-of-store)))))


(local (in-theory (disable SIGNED-BYTE-P)))

;bzo speed this up..
(defthm good-memoryp-of-store
  (implies (and (good-memoryp mem)
                ;a
                )
           (good-memoryp (mem::store a v mem)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use ((:instance rkeys-of-cdddr-of-store)
                 (:instance mem-tree-domain-after-store))
           :in-theory (e/d (good-memoryp
                            ;MEM::MEM-TREE-DOMAIN
                            )
                           (SET::ALL-STRATEGY<NOT-NATP-LESS-THAN-SIZE>
                            mem-tree-domain-after-store
                            SET::ALL-STRATEGY<NATP-LESS-THAN-SIZE>)))))

(defthm _memtree-p-of-list-nil
  (implies (not (zp depth))
           (not (mem::|_MEMTREE-P| '(nil) depth)))
  :hints (("Goal" :in-theory (enable mem::|_MEMTREE-P|))))

(defthm mem::domain-aux-iff
  (implies (mem::|_MEMTREE-P| mem-tree depth)
           (iff (mem::domain-aux mem-tree depth)
                mem-tree))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable MEM::DOMAIN-AUX
                              mem::|_MEMTREE-P|))))

(defthm domain-of-clear
  (implies (good-memoryp m)
           (equal (mem::domain (mem::clear p m))
                  (set::delete p (mem::domain m))))
  :hints (("Goal" :in-theory (enable mem::clear))))

(defthm good-memoryp-of-clear
  (implies (acl2::good-memoryp mem)
           (acl2::good-memoryp (mem::clear addr mem)))
  :hints (("Goal" :in-theory (enable mem::clear))))

;; We could instead use zero as the default value, I guess.
(defund mem::clear (addr mem)
  (declare (xargs :guard (and (mem::memory-p mem)
                              (mem::address-p addr mem))))
  (mem::store addr nil mem))


(defthm clear-over-clear
  (implies (not (equal a1 a2))
           (equal (mem::clear a1 (mem::clear a2 r))
                  (mem::clear a2 (mem::clear a1 r))))
  :hints (("Goal" :in-theory (enable mem::clear))))

(defthm clear-of-clear
  (equal (mem::clear a (mem::clear a r))
         (mem::clear a r))
  :hints (("Goal" :in-theory (enable mem::clear))))

(defthm clear-over-store
  (equal (mem::clear a1 (mem::store a2 v r))
         (if (equal a1 a2)
             (mem::clear a1 r)
           (mem::store a2 v (mem::clear a1 r))))
  :hints (("Goal" :in-theory (enable mem::clear))))

(defthm load-of-clear
  (equal (mem::load a1 (mem::clear a2 r))
         (if (equal a1 a2) nil
           (mem::load a1 r)))
  :hints (("Goal" :in-theory (enable mem::clear))))


(defthm consp-of-new
  (consp (mem::new size))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable mem::new))))

;;
;; The "clr" function
;;

(defund clr (a r)
  (declare (type t a r))
  (s a nil r))

(defthm clr-over-clr
  (implies
   (not (equal a1 a2))
   (equal (clr a1 (clr a2 r))
          (clr a2 (clr a1 r))))
  :hints (("Goal" :in-theory (enable clr))))

(defthm clr-of-clr
  (equal (clr a (clr a r))
         (clr a r))
  :hints (("Goal" :in-theory (enable clr))))

(defthm clr-over-s
  (equal (clr a1 (s a2 v r))
         (if (equal a1 a2)
             (clr a1 r)
           (s a2 v (clr a1 r))))
  :hints (("Goal" :in-theory (enable clr))))

(defthm g-of-clr
  (equal (g a1 (clr a2 r))
         (if (equal a1 a2)
             nil
           (g a1 r)))
  :hints (("Goal" :in-theory (enable clr))))

(defun failed-location (tag)
  (declare (ignore tag))
  nil)

(defthm not-failed-location
  (implies
   (failed-location x)
   nil)
  :rule-classes (:forward-chaining))

(in-theory (disable failed-location (failed-location) (:type-prescription failed-location)))

(defun tag-location (tag b)
  (implies (not b)
           (failed-location tag)))

(defthmd tag-location-elimination
  (iff (tag-location tag b) b)
  :hints (("goal" :in-theory (enable failed-location))))

(in-theory (disable (tag-location)))

(in-theory (e/d (tag-location-elimination) (tag-location)))

; jcd - extracted this from later encapsulate and made it local to this book
; so that it won't be exported
(local (defthm s-aux-is-bounded
         (implies (and (rcdp r)
                       (s-aux a v r)
                       (<< e a)
                       (<< e (caar r)))
                  (<< e (caar (s-aux a v r))))))

; jcd - extracted this from later encapsulate and made it local to this book
; so that it won't be exported
(local (defthm s-aux-preserves-rcdp
         (implies (rcdp r)
                  (rcdp (s-aux a v r)))))

; jcd - made this local to this book, so it won't be exported
(local (defthm acl2-count-of-g-aux-bound
         (<= (acl2-count (acl2::g-aux a r))
             (acl2-count r))
         :hints (("Goal" :do-not '(generalize eliminate-destructors)))))

(defthm acl2-count-of-g-bound
  (<= (acl2-count (g a r)) (acl2-count r))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable g acl2::g-aux ACL2::ACL2->RCD ))))

; jcd - made this local to this book, so it won't be exported
(local (defthm iff-s-aux-cases
         (implies (rcdp r)
                  (iff (s-aux a v r)
                       (not (or (and (ENDP R)
                                     (not V))
                                (and (consp r)
                                     (not v)
                                     (EQUAL A (CAAR R))
                                     (not (cdr r)))))))))

; jcd - change this to more simple if form
; was: (defun wfkey (k)
;        (declare (type t k))
;        (not (not k)))

(defun wfkey (k)
  (declare (type t k))
  (if k t nil))

;; (defun wfkeys (list)
;;   (declare (type t list))
;;   (if (consp list)
;;       (and (wfkey (car list))
;;            (wfkeys (cdr list)))
;;     t))

(defun wfkeyed (r)
  (declare (type t r))
  (if (consp r)
      (and (consp (car r))
           (wfkey (caar r))
           (wfkeyed (cdr r)))
    t))

; jcd - made this local to this book, so it won't be exported
(local (defthm not-ifrp-s-aux
         (implies (and
                   (not (ifrp r))
                   (rcdp r)
                   (wfkeyed r)
                   (wfkey a))
                  (not (ifrp (s-aux a v r))))
         :hints (("goal" :induct (s-aux a v r)))))

; jcd - made this local to this book, so it won't be exported
; ews - doh! I needed this (at least temporarily) to be non-local
(local
 (defthm wfkeyed-s-aux
         (implies (and (not (ifrp r))
                       (rcdp r)
                       (wfkeyed r)
                       (wfkey a))
                  (wfkeyed (s-aux a v r)))
         :hints (("goal" :induct (s-aux a v r))))
)

(defun wfr (r)
  (declare (type t r))
  (and (rcdp r)
       (not (ifrp r))
       (wfkeyed r)))

(defthm wfr-implies
  (implies
   (wfr r)
   (and (rcdp r)
       (not (ifrp r))
       (wfkeyed r)))
  :rule-classes (:forward-chaining))

; jcd - made this local to this book, so it won't be exported
(local (defthm wfr-s-aux
         (implies (and (wfr r) (wfkey a))
                  (wfr (s-aux a v r)))))

;; when can s-aux be nil?
(defthm s-preserves-wfr
  (implies (and (wfkey a) (wfr r))
           (wfr (s a v r)))
  :hints (("goal" :in-theory (enable s acl2->rcd rcd->acl2))))


; jcd - made this local to this book, so it won't be exported
(local (defthm acl2-count-g-aux-decreases
         (implies (and (wfr r)
                       (g-aux a r))
                  (< (acl2-count (g-aux a r))
                     (acl2-count r)))
         :hints (("goal" :induct (g-aux a r)))))

(defthm acl2-count-g-decreases
  (implies (and (wfr r)
                (g a r))
           (< (acl2-count (g a r))
              (acl2-count r)))
  :hints (("goal" :in-theory (enable g acl2->rcd)))
  :rule-classes (:linear :rewrite))

(in-theory (disable clr
                    wfr
                    wfkey
                    wfkeyed ; jcd - added wfkeyed
;                    wfkeys
                    ))

(defthm s-when-v-and-r-are-nil
  (equal (s key nil nil)
         nil))

(defthm clr-of-nil
  (equal (clr key nil)
         nil)
  :hints (("Goal" :in-theory (e/d (clr) (S==R)))))

;prove with lemmas instead of enabling
(defthm clr-when-r-is-not-a-consp
  (implies (not (consp r))
           (equal (clr nil r)
                  nil))
  :hints (("Goal" :in-theory (e/d (clr s acl2->rcd) (S==R)))))

;This is true even when the key is nil.
(defthm wfr-of-clr
  (implies (wfr r)
           (wfr (clr key r)))
  :hints (("Goal" :cases (key)
           :in-theory (e/d (clr wfkey) (S==R)))))

(defthm wfkeyed-of-s
  (implies (and (wfr r)
                (wfkey key)
                (wfkeyed r))
           (wfkeyed (s key v r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use (:instance S-PRESERVES-WFR (a key))
           :in-theory (e/d (wfr  WFKEY RCD->ACL2
                                 ) (S-PRESERVES-WFR)))))

(defthmd s-becomes-clr
  (equal (s a nil r)
         (clr a r)))

;; Here we define a "set" version of rkeys.

(defun rkeys (r)
  (declare (type t r))
  (list::2set (acl2::rkeys r)))

(defthm setp-rkeys
  (setp (rkeys r)))

(defthm rkeys-of-s
  (equal (rkeys (acl2::s a v r))
         (if (null v) (delete a (rkeys r))
           (insert a (rkeys r)))))

(defthm rkeys-of-clr
  (equal (rkeys (acl2::clr a r))
         (delete a (rkeys r))))

;; Is this what we want?  Or should we stick with forward chaining, as
;; with (consp (rkeys ..)) ??

(defthm empty-rkeys-not-r
  (equal (empty (rkeys r))
         (not r))
  ;;:rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (e/d nil
                                  (EMPTY-WHEN-SETP-MEANS-NIL)))))

(defthm rkeys-iff-r
  (iff (set::rkeys r) r)
  :hints (("Goal" :in-theory (e/d (set::rkeys) (set::2SET-REWRAP))
           :expand (list::2set (acl2::rkeys r)))))

(defthm not-memberp-r
  (implies
   (not (in a (rkeys r)))
   (equal (acl2::clr a r) r)))

(defthm memberp-g
  (implies
   (in a (rkeys r))
   (acl2::g a r))
  :rule-classes (:forward-chaining))

(defthm non-memberp-g
  (implies
   (not (in a (rkeys r)))
   (not (acl2::g a r)))
  :rule-classes (:forward-chaining))

(defthm wfr-implies-nil-not-in-rkeys
  (implies
   (acl2::wfr tr)
   (not (in nil (rkeys tr)))))

(in-theory (disable rkeys))

#|
(defun key-set (r)
  (if (consp r)
      (set::insert (caar r)
                   (key-set (cdr r)))
    (set::emptyset)))

(defthm setp-key-set
  (set::setp (key-set r)))

(defund rkeys (r)
  (key-set (acl2->rcd r)))

(defthm setp-of-rkeys
  (set::setp (rkeys r))
  :hints (("Goal" :in-theory (enable rkeys))))

(defthm in-key-set-s-aux-better
  (implies (not (ifrp r))  ;(wfr r)
           (equal (set::in a (key-set (s-aux p v r)))
                  (if v (or (equal a p)
                            (set::in a (key-set r)))
                    (and (not (equal a p))
                         (set::in a (key-set r))))))
  :hints (("goal" :in-theory (e/d (wfkeyed wfr s-aux) ()))))

(defthm rkeys-of-clr
  (equal (rkeys (clr key r))
         (set::delete key (rkeys r)))
  :hints (("Goal" :in-theory (e/d (clr) (S==R)))))

;bzo make a t-p rule?
(defthm rkeys-iff
  (iff (rkeys r)
       r)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable RKEYS ACL2->RCD))))

(defthm rkeys-non-nil-tp
  (implies r
           (rkeys r))
  :rule-classes (:type-prescription))

;do we need all of these?

(defthm empty-of-rkeys
  (equal (set::empty (rkeys r))
         (equal r nil))
  :hints (("Goal" :in-theory (enable rkeys acl2->rcd))))

(defthm rkeys-when-not-consp
  (implies (not (consp r))
           (equal (RKEYS R)
                  (if (equal r nil)
                      nil
                    (list nil))))
  :hints (("Goal" :in-theory (enable rkeys ACL2->RCD))))
|#
