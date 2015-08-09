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



; memory-impl.lisp
;
; This is an implementation file and should not be directly included in
; external work.  Use the interface file (memory.lisp) instead!
;
; In this file we are interested in defining the user-visible notion of
; memories, and the functions to load and store into them.  We want to take
; advantage of the records library in order to provide the same record book
; theorems about our memories.

(in-package "MEM")
(set-verify-guards-eagerness 2)

(include-book "log2")
(include-book "memtree")
(include-book "misc/records" :dir :system)



; Definition of memories.  A memory is a relatively complicated structure
; which combined several components:
;
;   mtree  - a memtree (see the included book "memtree")
;   depth  - the depth of mtree
;   size   - the logical size of this memory (0 <= size < (expt 2 depth)
;   fast   - a flag indicating if depth is a fixnum (almost always t)
;   record - an ACL2 record ("misc/records")
;
; Here is the basic idea.  Memtrees are really pretty nice all on their own,
; but they are limited in that (1) you always have to keep track of their
; depth, (2) their size can only be a power of 2, and (3) their addresses must
; all be numeric, complicating the theorems about them.
;
; With memories, we hope to solve all of these problems.  (1) is addressed
; simply by storing the depth of the mtree, (2) is addressed by keeping a
; separate field for the memtree's size, and (3) is addressed by adding a
; standard record which will be used (logically) to store any non-address
; fields.
;
; Our ultimate goal is to provide, for memories, the exact same theorems that
; the records book provides for records.  In other words, we want memories to
; be no more difficult to reason about than records, while still providing high
; efficiency through the use of memtrees.

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

(defthm memory-p-is-boolean
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

(defthm memory-p-of-new
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

(defthm size-of-new
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

(encapsulate
 nil

 (local (defthm address-p-redefinition
          (implies (memory-p mem)
                   (equal (address-p addr mem)
                          (and (natp addr)
                               (< addr (_memory-size mem)))))))

 (local (in-theory (disable address-p)))

 (defthm _store-memory
   (_memory-p (_store addr elem mem))
   :hints(("Goal" :in-theory (enable _memory-p))))

)

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

(defthm load-of-same-store
  (equal (load a (store a elem mem))
         elem))

(defthm load-of-store-when-diff
  (implies (not (equal a b))
           (equal (load a (store b elem mem))
                  (load a mem))))

(defthm store-of-same-store
  (equal (store a e1 (store a e2 mem))
         (store a e1 mem)))

(defthm store-of-store-when-diff
  (implies (not (equal a b))
           (equal (store a e1 (store b e2 mem))
                  (store b e2 (store a e1 mem)))))

(defthm store-of-same-load
  (equal (store a (load a mem) mem)
         mem))





;;; That's the main record lemmas.  Now we want to add our own guard lemmas.

(defthm load-of-new
  (equal (load addr (new size))
         nil))

(defthm memory-p-of-store
  (implies (memory-p mem)
           (memory-p (store addr elem mem))))

(defthm size-of-store
  (implies (memory-p mem)
           (equal (size (store addr elem mem))
                  (size mem))))


