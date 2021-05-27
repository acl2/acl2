; ACL2 Version 8.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Regarding authorship of ACL2 in general:

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; hons-raw.lisp -- Raw lisp implementation of hash cons and fast alists.  Note
; that the memoization and watch functionality previously provided by this file
; have been moved into memoize-raw.lisp.  This file has undergone a number of
; updates and changes since its original creation in about 2005.

; The original version of this file was contributed by Bob Boyer and Warren
; A. Hunt, Jr.  The design of this system of Hash CONS, function memoization,
; and fast association lists (applicative hash tables) was initially
; implemented by Boyer and Hunt.  The code was subsequently improved by Boyer
; and Hunt, and also by Sol Swords, Jared Davis, and Matt Kaufmann.  This file
; is now maintained by the ACL2 authors (see above).

; This code is well commented and the comments have been contributed and
; improved by all of the authors named above.  However, comments referring to
; "I" or "my" are from Jared, as is the token "BOZO" which he uses to leave
; a note about a wart or modification to consider.

; Despite the comments here, we recommend reading the user-level documentation
; for HONS-AND-MEMOIZATION before diving into this code.

(in-package "ACL2")

; NOTES ABOUT HL-HONS
;
; The "HL-" prefix was introduced when Jared Davis revised the Hons code, and
; "HL" originally meant "Hons Library."  The revision included splitting the
; Hons code from the function memoization code, and took place in early 2010.
; We will now use the term to refer to the new Hons implementation that is
; found below.  It might be helpful to read the Essay on Hons Spaces before
; proceeding.

; Some changes made in HL-Hons, as opposed to the old Hons system, include:
;
;   - We combine all of the special variables used by the Hons code into an
;     explicit Hons-space structure.
;
;   - We no longer separately track the length of sbits.  This change appears
;     to incur an overhead of 3.35 seconds in a 10-billion iteration loop, but
;     gives us fewer invariants to maintain and makes Ctrl+C safety easier.
;
;   - We have a new static honsing scheme where every normed object has an
;     address, and NIL-HT, CDR-HT, and CDR-HT-EQL aren't needed when static
;     honsing is used.
;
;   - Since normed strings are EQ comparable, we now place cons pairs whose
;     cdrs are strings into the CDR-HT hash table instead of the CDR-HT-EQL
;     hash table in classic honsing.
;
;   - Previously, fast alists were essentially implemented as flex alists.
;     (See the essay about flex alists for an introduction to these
;     structures.)  Now we always create a hash table instead.  This slightly
;     simplifies the code and results in trivially fewer runtime type checks in
;     HONS-GET and HONS-ACONS.  Our implementation does still use flex alists
;     under the hood to implement classic honsing (specifically, in the CDR-HT
;     and CDR-HT-EQL fields of a hons space), where we can imagine often
;     finding cdrs for which we don't have at least 18 separate cars.  But fast
;     alists are much more targeted; if ACL2 users are building fast alists, it
;     seems very likely that they know they are doing something big (or
;     probably big) -- otherwise they wouldn't be bothering with fast alists.


; ESSAY ON CTRL+C SAFETY
;
; The HL-Hons implementation involves certain impure operations.  Sometimes, at
; intermediate points during a sequence of updates, the invariants on a Hons
; Space are violated.  This is dangerous because a user can interrupt at any
; time using 'Ctrl+C', leaving the system in an inconsistent state.
;
; We have tried to avoid sequences of updates that violate invariants.  In the
; rare cases where this isn't possible, we need to protect the sequence of
; updates with 'without-interrupts'.  We assume that SETF itself does not
; suffer from this kind of problem and that the Lisp implementation should
; ensure that, e.g., (SETF (GETHASH ...)) does not leave a hash table in an
; internally inconsistent state.

; CROSS-LISP COMPATIBILITY WRAPPERS
;
; As groundwork toward porting the static honsing scheme to other Lisps that
; might be able to support it, we have added these wrappers for various ccl::
; functionality.

(defun hl-mht-fn (&key (test             'eql)
                       (size             '60)
                       (rehash-size      '1.5)
                       (rehash-threshold '0.7)
                       (weak             'nil)
                       (shared           'nil)
                       (lock-free        'nil))

; See hl-mht.  Here we have a special hack: if :shared is :default then we
; leave it to the underlying Lisp (in particular CCL) to decide about :shared
; and :lock-free.

  (declare (ignorable shared weak lock-free))
  (cond ((eq shared :default)
         (make-hash-table :test             test
                          :size             size
                          :rehash-size      rehash-size
                          :rehash-threshold rehash-threshold
                          #+ccl :weak #+sbcl :weakness
                          #+(or ccl sbcl) weak
                          ))
        (t
         (make-hash-table :test             test
                          :size             size
                          :rehash-size      rehash-size
                          :rehash-threshold rehash-threshold
                          #+ccl :weak #+sbcl :weakness
                          #+(or ccl sbcl) weak
                          #+ccl :shared #+ccl shared
                          #+ccl :lock-free #+ccl lock-free
                          ))))

#+allegro
(declaim (type hash-table *allegro-hl-hash-table-size-ht*))
#+allegro
(defvar *allegro-hl-hash-table-size-ht*
; See the comment about this hash table in hl-mht.
  (make-hash-table))

(defmacro hl-mht (&rest args)

; This macro is a wrapper for hl-mht-fn, which in turn is a wrapper for
; make-hash-table.  But here we have a special hack: if :shared is :default
; then we leave it to the underlying Lisp (in particular CCL) to decide about
; :shared and :lock-free.

; Because of our approach to threading, we generally don't need our hash tables
; to be protected by locks.  HL-MHT is essentially like make-hash-table, but on
; CCL creates hash tables that aren't shared between threads, which may result
; in slightly faster updates.

; In Allegro CL 9.0 (and perhaps other versions), make-hash-table causes
; creation of a hash table of a somewhat larger size than is specified by the
; :size argument, which can cause fast-alist-fork to create hash tables of
; ever-increasing size when this is not necessary.  The following example
; illustrates this problem, which was first observed in community book
; books/parsers/earley/earley-parser.lisp.

;   (defconst *end* :end)
;
;   (defn my-fast-alist-fork (a)
;     (let ((ans (fast-alist-fork a *end*)))
;       (prog2$ (fast-alist-free a)
;               ans)))
;
;   (defun my-fast-alist3 (n ans)
;     (declare (type (integer 0 *) n))
;     (cond ((zp n) ans)
;           (t (my-fast-alist3 (1- n)
;                              (my-fast-alist-fork
;                               (hons-acons (mod n 10) (* 10 n) ans))))))
;
;   (trace! (hl-mht-fn :native t :exit t))
;
;   (time$ (my-fast-alist3 33 *end*))

; Our solution is to use a hash table, *allegro-hl-hash-table-size-ht*, to map
; the actual size of a hash table, h, to the :size argument of the call of
; hl-mht that created h.  Then, when we want to create a hash table of a given
; :size, new-size-arg, we look in *allegro-hl-hash-table-size-ht* to check
; whether a previous call of hl-mht created a hash table of that size using
; some :size, old-size-arg, and if so, then we call make-hash-table with :size
; old-size-arg instead of new-size-arg.  (Note that we don't give this special
; treatment in the case that hl-mht is called without an explicit :size; but
; that seems harmless.)

  #-allegro
  `(hl-mht-fn ,@args)
  #+allegro
  (let ((tail (and (keyword-value-listp args)
                   (assoc-keyword :size args))))
    (cond (tail
           (let ((size-arg-var (gensym))
                 (old-size-arg-var (gensym)))
             `(let* ((,size-arg-var ,(cadr tail))
                     (,old-size-arg-var
                      (gethash ,size-arg-var *allegro-hl-hash-table-size-ht*)))
                (cond (,old-size-arg-var
                       (hl-mht-fn :size ,old-size-arg-var
                                  ,@(remove-keyword :size args)))
                      (t (let ((ht (hl-mht-fn ,@args)))
                           (setf (gethash (hash-table-size ht)
                                          *allegro-hl-hash-table-size-ht*)
                                 ,size-arg-var)
                           ht))))))
          (t `(hl-mht-fn ,@args)))))

; ESSAY ON STATIC CONSES

; In CCL, one can use (ccl::static-cons a b) in place of (cons a b) to create a
; cons that will not be moved by the garbage collector.
;
; Unlike an ordinary cons, every static cons has a unique index, which is a
; fixnum, and which may be obtained with (ccl::%staticp x).  Per Gary Byers,
; this index will be forever fixed, even after garbage collection, even after
; saving an image.
;
; Even more interesting, the cons itself can be recovered from its index using
; ccl::%static-inverse-cons.  Given the index of a static cons, such as
; produced by ccl::%staticp, %static-inverse-cons produces the corresponding
; static cons.  Given an invalid index (such as the index of a cons that has
; been garbage collected), %static-inverse-cons produces NIL.  Hence, this
; gives us a way to tell if a cons has been garbage collected, and lets us
; implement a clever scheme for "washing" honses.
;
; We now write wrappers for static-cons, %staticp, and %static-inverse-cons, to
; make it easier to plug in alternative implementations in other Lisps.

#+static-hons
(defmacro hl-static-cons (a b)
  #+gcl `(cons ,a ,b)
  #-gcl `(ccl::static-cons ,a ,b))

#+static-hons
(defmacro hl-staticp (x)

; This function always returns a fixnum.

; CCL::%STATICP always returns a fixnum or nil, as per Gary Byers email June
; 16, 2014.  That email also confirmed that if the value is not nil after a
; garbage collection, then the value is unchanged from before the garbage
; collection; and also, that the value remains unchanged after saving an image.

; Indeed, this function returns a fixnum (see also above) if x is a static
; cons.  More may be true, as follows, but we don't count on it: in mid-2014,
; at least, we see that for CCL, the value returned is 128 for the first static
; cons and is incremented by 1 for each additional static cons -- and after a
; garbage collection, this repeats except that values for remaining static
; conses are skipped.

; See also *hl-hspace-sbits-default-size*.

  #+gcl

; Camm Maguire tells us that conses are always 16-byte aligned in 64-bit GCL
; and 8-byte aligned in 32-bit GCL.

  `(the fixnum
        (ash (the fixnum (si::address ,x))
             #+x86_64 -4
             #-x86_64 -3))
  #-gcl
  `(ccl::%staticp ,x))

#+static-hons
(defmacro hl-static-inverse-cons (x)
  #+gcl `(si::static-inverse-cons (the fixnum (ash (the fixnum ,x)
                                                   #+x86_64 4
                                                   #-x86_64 3)))
  #-gcl `(ccl::%static-inverse-cons ,x))

#+static-hons
(defmacro hl-machine-hash (x)

; NOT A FUNCTION.  Note that (EQUAL (HL-MACHINE-HASH X) (HL-MACHINE-HASH X)) is
; not necessarily true, because objects may be moved during garbage collection
; in CCL.
;
; We use the machine address of an object to compute a hash code within [0,
; 2^20).  We obtain a good distribution on 64-bit CCL, but we have not tried
; this on 32-bit CCL.
;
; We use the CCL primitive ccl::strip-tag-to-fixnum because it always returns a
; fixnum, while ccl::%address-of (which returns the machine address) might
; conceivably not do so, according to email 6/2014 from Gary Byers.  He
; explains that CCL uses ccl::strip-tag-to-fixnum "to derive a fixnum from its
; argument's address (it effectively does something like a right shift by 4
; bits....".
;
; For CCL, we right-shift the address by five places because smaller shifts led
; to worse distributions.  (GCL wart: We haven't really thought this efficiency
; issue through for GCL.)  Gary Byers has informed us (email, 6/16/2014) that
; in 64-bit CCL, memory-allocated objects (like conses) are 16-byte aligned,
; and the bottom 4 bits (all 0) are replaced by tag bits (where those tag bits
; are always 3 for a cons).  So shifting by 4 bits might seem to suffice, but
; we got a significantly better distribution shifting by 5 bits (see discussion
; of experiments below, "However, in addition to fast execution speed....").
;
; It should be easy to change this from 2^20 to other powers of 2.  We think
; 2^20 is a good number, since a 2^20 element array seems to require about 8 MB
; of memory, e.g., our whole cache (which consists of two such arrays; see
; "Implementation 2" of Cache Tables, below) will take 16 MB.
;
  `(the fixnum (ash (the fixnum
                         (logand #x1FFFFF
                                 #+gcl (ash (si::address ,x) -4)
                                 #+ccl (ccl::strip-tag-to-fixnum ,x)
                                 #-(or gcl ccl)
                                 (error "~s is not implemented in this Lisp."
                                        'hl-machine-hash)
                                 #-(or gcl ccl)
                                 0))
                    -1)))


; ----------------------------------------------------------------------
;
;                           CACHE TABLES
;
; ----------------------------------------------------------------------

; A Cache Table is a relatively simple data structure that can be used to
; (partially) memoize the results of a computation.  Cache tables are used by
; the hons implementation, but are otherwise independent from the rest of hons.
; We therefore introduce them here, up front.
;
; The operations of a Cache Table are as follows:
;
;    (HL-CACHE-GET KEY TABLE)         Returns (MV PRESENT-P VAL)
;    (HL-CACHE-SET KEY VAL TABLE)     Destructively modifies TABLE
;
; In many ways, a Cache Table is similar to an EQ hash table, but there are
; also some important differences.  Unlike an ordinary hash table, a Cache
; Table may "forget" some of its bindings at any time.  This allows us to
; ensure that the Cache Table does not grow beyond a fixed size.
;
; Cache Tables are not thread safe.
;
; We have two implementations of Cache Tables.
;
; Implementation 1.  For Lisps other than 64-bit CCL (#-static-hons).
;
;    A Cache Table is essentially an ordinary hash table, along with a separate
;    field that tracks its count.
;
;    It is almost an invariant that this count should be equal to the
;    HASH-TABLE-COUNT of the hash table, but we do NOT rely upon this for
;    soundness and this property might occasionally be violated due to
;    interrupts.  In such cases, we ensure that the count is always more than
;    the HASH-TABLE-COUNT of the hash table.  (The only negative consequence of
;    this is that the table may be cleared more frequently.)
;
;    The basic scheme is as follows.  Whenever hl-cache-set is called, if the
;    count exceeds our desired threshold, we clear the hash table before we
;    continue.  The obvious disadvantage of this is that we may throw away
;    results that may be useful.  But the advantage is that we ensure that the
;    cache table does not grow.  On one benchmark, this approach was about
;    17% slower than letting the hash table grow without restriction (notably
;    ignoring all garbage collection costs), but it lowered the memory usage
;    from 2.8 GB to 92 MB.
;
;    We have considered improving the performance by experimenting with the
;    size of its cache.  A larger cache means less frequent clearing but
;    requires more memory.  We also looked into more smartly clearing out the
;    cache.  One idea was to throw away only half of the entries "at random" by
;    just allowing the maphash order to govern whether we throw out one entry
;    or another.  But when this was slow, we discovered that, at least on CCL,
;    iterating over a hash table is fairly expensive and requires the keys and
;    values of the hash table to be copied into a list.  For a 500k cache,
;    "clearing" half the entries required us to allocate 6 MB, and ruined
;    almost all memory savings we had hoped for.  Hence, we just use ordinary
;    clrhash.
;
; Implementation 2.  For 64-bit CCL (#+static-hons) we use a better scheme.
;
;    A Cache Table contains two arrays, KEYDATA and VALDATA.  These arrays
;    associate "hash codes" (array indices) to keys and values, respectively.
;    We could have used a single array with (key . val) pairs as its entries,
;    but using two separate arrays allows us to implement hl-cache-set with no
;    consing.
;
;    These hash codes are based upon the actual machine address of KEY, and
;    hence (1) may easily collide and (2) are not reliable across garbage
;    collections.  To give a sensible semantics, in hl-cache-get, we must
;    explicitly check that this hash code has the proper KEY.
;
;    Our hashing function, hl-machine-hash, performs quite well.  According to
;    a rough test, it takes only about the same time as about 11 fixnum
;    additions.  Just below is a log of our tests (on a 2010 MacBook Pro).
;
;      ? (defun f (x)
;          (let ((acc 0))
;            (declare (type fixnum acc))
;            (loop for i fixnum from 1 to 1000000000
;                  do
;                  (setq acc (the fixnum (+ (the fixnum acc) (the fixnum (car x)))))
;                  (setq acc (the fixnum (+ (the fixnum acc) (the fixnum (cdr x)))))
;                  (setq acc (the fixnum (+ (the fixnum acc) (the fixnum (car x)))))
;                  (setq acc (the fixnum (+ (the fixnum acc) (the fixnum (cdr x)))))
;                  (setq acc (the fixnum (+ (the fixnum acc) (the fixnum (car x)))))
;                  (setq acc (the fixnum (+ (the fixnum acc) (the fixnum (cdr x)))))
;                  (setq acc (the fixnum (+ (the fixnum acc) (the fixnum (car x)))))
;                  (setq acc (the fixnum (+ (the fixnum acc) (the fixnum (cdr x)))))
;                  (setq acc (the fixnum (+ (the fixnum acc) (the fixnum (car x)))))
;                  (setq acc (the fixnum (+ (the fixnum acc) (the fixnum (cdr x)))))
;                  (setq acc (the fixnum (+ (the fixnum acc) (the fixnum (car x)))))
;                  )
;            acc))
;      F
;      ? (defun g (x)
;          (let ((acc 0))
;            (declare (type fixnum acc))
;            (loop for i fixnum from 1 to 1000000000
;                  do
;                  (setq acc (the fixnum (hl-machine-hash (car x)))))
;            acc))
;      G
;      ? (time (f '(1 . 2)))
;      (F '(1 . 2))
;      took 3,398,028 microseconds (3.398028 seconds) to run.
;      During that period, and with 4 available CPU cores,
;           3,394,546 microseconds (3.394546 seconds) were spent in user mode
;               1,643 microseconds (0.001643 seconds) were spent in system mode
;      16000000000
;      ? (time (g '((1 . 2))))
;      (G '((1 . 2)))
;      took 3,387,291 microseconds (3.387291 seconds) to run.
;      During that period, and with 4 available CPU cores,
;           3,384,752 microseconds (3.384752 seconds) were spent in user mode
;               1,501 microseconds (0.001501 seconds) were spent in system mode
;      90258
;      ?
;
;    However, in addition to fast execution speed, we want this function to
;    produce a good distribution so that we may hash on its result.  We have
;    hard-coded in a size of 2^20 for our data arrays, but it would not be very
;    hard to change this.  To determine how well it distributes addresses, we
;    computed the hash codes for a list of 2^24 objects, which is more than the
;    2^20 hash codes that we have made available.  We found that every hash
;    code was used 15, 16, or 17 times, a nearly perfect distribution!  (Of
;    course, when this is used on actual data produced by a program, we do not
;    expect the results to be so good.)  Here is some basic testing code:
;
;      (include-book "std/osets/sort" :dir :system)
;      (include-book "defsort/duplicated-members" :dir :system)
;
;      (defparameter *hashes* nil)
;
;      (let* ((tries        (expt 2 24))
;             (hashes       (time (loop for i fixnum from 1 to tries collect
;                                       (hl-machine-hash (cons 1 2)))))
;             (nhashes      (time (len (set::mergesort hashes)))))
;        (setq *hashes* hashes)
;        (format t "Got ~:D entries for ~:D tries.~%" nhashes tries))
;
;      (defparameter *dupes* (hons-duplicity-alist *hashes*))
;      (set::mergesort (strip-cdrs *dupes*))
;
;    Result: "Got 1,048,576 entries for 16,777,216 tries."
;
;    Result: (set::mergesort (strip-cdrs *dupes*)) is (15 16 17).
;
;    Specifically, execution of
;
;    (let ((ans nil))
;         (loop for pair in *dupes* as n = (cdr pair)
;          do (setq ans (put-assoc n (1+ (or (cdr (assoc n ans)) 0)) ans))
;          finally (return ans)))
;
;    returned:
;
;    ((15 . 93880) (16 . 860816) (17 . 93880))
;
;    However, when we only shifted four bits of the machine address using
;
;    `(logand #xFFFFF (hl-machine-address-of ,x))
;
;    for the body of hl-machine-hash, we got a much worse distribution that
;    used only half the hash codes, perhaps because of how CCL implements
;    ccl::%address-of on Darwin (as these experiments were on a Mac).
;
;    ((31 . 88652) (33 . 96844) (32 . 334696) (30 . 4096))
;
;    We also tried shifting six bits of the address using
;
;    `(ash (the fixnum (logand #x3FFFFF (hl-machine-address-of ,x))) -2)
;
;    for the body of hl-machine-hash, but that distribution was also not as
;    good:
;
;    ((16 . 198089) (14 . 422171) (18 . 426266) (17 . 2) (12 . 2048))

; BOZO:  Implicitly, our cache table has NIL bound to NIL; this might not
;        be appropriate for "memoizing" other applications.

#-static-hons
(defconstant hl-cache-table-size
  ;; Size of the cache table
  400000)

#-static-hons
(defconstant hl-cache-table-cutoff
  ;; How full a cache table (e.g., the norm-cache of a hons space) can get
  ;; before we clear it.  This also becomes the maximum possible value of
  ;; the count field (see hl-cache-set).  Must be a fixnum.
  (let ((ans (floor (* 0.75 hl-cache-table-size))))
    (cond ((> ans most-positive-fixnum)
           (error "Hl-cache-table-cutoff is too big to be a fixnum!"))
          (t ans))))

(defstruct hl-cache

  #+static-hons
  (keydata   (make-array (expt 2 20) :initial-element nil) :type simple-vector)
  #+static-hons
  (valdata   (make-array (expt 2 20) :initial-element nil) :type simple-vector)

  #-static-hons
  (table     (hl-mht :test #'eq :size hl-cache-table-size) :type hash-table)
  #-static-hons
  (count     0

; Function hl-cache-set guarantees that count is a fixnum.

             :type fixnum))

(defun hl-cache-set (key val cache)
  (declare (type hl-cache cache))

  #+static-hons
  (let ((keydata (hl-cache-keydata cache))
        (valdata (hl-cache-valdata cache))
        (code    (hl-machine-hash key)))
    (without-interrupts
     (setf (svref keydata (the fixnum code)) key)
     (setf (svref valdata (the fixnum code)) val)))

  #-static-hons
  (let ((table (hl-cache-table cache))
        (count (hl-cache-count cache)))
    ;; This is a funny ordering which is meant to ensure the count exceeds or
    ;; agrees with (hash-table-count table), even in the face of interrupts.
    (cond ((>= (the fixnum count)
               (the fixnum hl-cache-table-cutoff))
           (clrhash table)
; We set count to one, not zero, because we're about to add an element.
           (setf (hl-cache-count cache) 1))
          (t (setf (hl-cache-count cache)
; Since count < hl-cache-table-cutoff, (+ 1 count) is guaranteed to be a
; fixnum.
                   (the fixnum (+ 1 (the fixnum count))))))
    (setf (gethash key table) val)))

(defun hl-cache-get (key cache)

; (HL-CACHE-GET KEY CACHE) --> (MV PRESENT-P VAL)
;
; WARNING: Key must not be nil, at least in the case #+static-hons (see
; below).
;
; Parallelism wart: Note that this isn't thread-safe.  If we want a truly
; multithreaded hons, we'll need to think about how to protect access to the
; cache.

  (declare (type hl-cache cache))

  #+static-hons
  (let* ((keydata  (hl-cache-keydata cache))
         (code     (hl-machine-hash key))
         (elem-key (svref keydata (the fixnum code))))

    (if (eq elem-key key) ; assumption: not :initial-element of keydata, nil
        (let* ((valdata  (hl-cache-valdata cache))
               (elem-val (svref valdata (the fixnum code))))
          (mv t elem-val))
      (mv nil nil)))

  #-static-hons
  (let* ((table (hl-cache-table cache))
         (val   (gethash key table)))
    (if val
        (mv t val)
      (mv nil nil))))

(defun hl-cache-clear (cache)
  (declare (type hl-cache cache))
  #+static-hons
  (let ((keydata (hl-cache-keydata cache))
        (valdata (hl-cache-valdata cache)))
    (loop for i fixnum below (expt 2 20) do
          (setf (svref keydata i) nil)
          (setf (svref valdata i) nil)))

  #-static-hons
  (progn
    ;; This ordering ensures count >= (hash-table-count table) even in
    ;; the face of interrupts
    (clrhash (hl-cache-table cache))
    (setf (hl-cache-count cache) 0)))


; ESSAY ON HONS SPACES
;
; The 'ACL2 Objects' are described in the ACL2 function bad-lisp-objectp;
; essentially they are certain "good" symbols, characters, strings, and
; numbers, recursively closed under consing.  Note that live stobjs are not
; ACL2 Objects under this definition.
;
; The 'Hons Spaces' are fairly complex structures, introduced with the
; defstruct for hl-hspace, which must satisfy certain invariants.  At any time
; there may be many active Hons Spaces, but separate threads may never access
; the same Hons Space!  This restriction is intended to minimize the need to
; lock while accessing Hons Spaces.
;
;    Aside.  Sharable Hons Spaces might have some advantages.  They might
;    result in lower overall memory usage and reduce the need to re-hons data
;    in multiple threads.  They might also be a better fit for ACL2(p)'s
;    parallelism routines.  But acquiring locks might slow honsing in
;    single-threaded code and make our code more complex.  Parallelism wart: We
;    may investigate this later.
;
;
; Fundamental Operations.
;
; A Hons Space provides two fundamental operations.
;
; First, given any ACL2 Object, X, and any Hons Space HS, we must be able to
; determine whether X is 'normed' with respect to HS.  The fundamental
; invariant of normed objects is that if A and B are both normed with respect
; to HS, then (EQUAL A B) holds iff (EQL A B).
;
; Second, given any ACL2 Object, X, and any Hons Space, HS, we must be able to
; 'norm' X to obtain an ACL2 Object that is EQUAL to X and which is normed with
; respect to HS.  Note that norming is 'impure' and destructively modifies HS.
; This modification is really an extension: any previously normed object will
; still be normed, but previously non-normed objects may now also be normed.
;
;
; Tracking Normed Objects.
;
; To support these operations, a Hons Space contains certain hash tables and
; arrays that record which ACL2 Objects are currently regarded as normed.
;
; Symbols, characters, and numbers.  These objects automatically and trivially
; satisfy the fundamental invariant of normed objects.  We therefore regard all
; symbols, characters, and numbers as normed with respect to any Hons Space,
; and nothing needs to be done to track whether particular symbols, characters,
; or numbers are normed.
;
; Strings.  Within each Hons Space, we may choose some particular string, X, as
; the normed version of all strings that are equal to X.  We record this choice
; in the STR-HT field of the Hons Space, which is an EQUAL hash table.  The
; details of what we record in the STR-HT actually depend on whether 'classic
; honsing' or 'static honsing' is being used.  See below.
;
; Conses.  Like strings, there are EQUAL conses which are not EQL.  We could
; account for this by setting up another equal hash table, as we did for
; strings, but EQUAL hashing of conses can be very slow.  More efficient
; schemes are possible because we insist upon two reasonable invariants:
;
;   INVARIANT C1.  The car of a normed cons must be normed.
;   INVARIANT C2.  The cdr of a normed cons must be normed.
;
; Using these invariants, we have developed two schemes for tracking which
; conses are normed.  One approach, called classic-honsing, makes use of only
; ordinary Common Lisp functions.  The second approach, static-honsing, is
; higher performance but requires features that are specific to Clozure Common
; Lisp.


; ESSAY ON CLASSIC HONSING
;
; Prerequisite: see the essay on hons spaces.
;
; Classic Honsing is a scheme for tracking normed conses that can be used in
; any Lisp.  Here, every normed cons is recorded in one of three hash tables.
; In particular, whenever X = (A . B) is normed, then X will be found in
; either:
;
;    NIL-HT, when B is NIL,
;    CDR-HT, when B is a non-NIL symbol, a cons, or a string, or
;    CDR-HT-EQL otherwise.
;
; The NIL-HT binds A to X whenever X = (A . NIL) is a normed cons.  Thanks to
; Invariant C1, which assures us that A will be normed, we only need to use an
; EQL hash table for NIL-HT.
;
; For other conses, we basically implement a two-level hashing scheme.  To
; determine if a cons is normed, we first look up its CDR in the CDR-HT or
; CDR-HT-EQL, depending on its type.  Both of these tables bind B to the set of
; all normed X such that X = (A . B) for any A.  These sets are represented as
; 'flex alists', defined later in this file.  So, once we have found the proper
; set for B, we look through it and see whether there is a normed cons in it
; with A as its CAR.
;
; We use the CDR-HT (an EQ hash table) for objects whose CDRs are
; EQ-comparable, and the CDR-HT-EQL (an EQL hash table) for the rest.  We may
; use CDR-HT for both strings and conses since, by Invariant C2, we know that
; the CDR is normed and hence pointer equality suffices.
;
; The only other thing to mention is strings.  In the classic honsing scheme,
; the STR-HT simply associates each string to its normed version.  That is, a
; string X is normed exactly when (eq X (gethash X STR-HT)).  It is
; straightforward to norm a string X: a STR-HT lookup (using EQUAL) tells us
; whether a normed version of X exists and, if so, what it is.  Otherwise, when
; no normed version of X exists, we effectively 'norm' X by extending the
; STR-HT by binding X to itself.
;
; Taken all together, the STR-HT, NIL-HT, CDR-HT, and CDR-HT-EQL completely
; determine which ACL2 objects are normed in the classic honsing scheme.


; ESSAY ON STATIC HONSING
;
; Prerequisite: see the Essay on Hons Spaces and the Essay on Static Conses.
;
; Static Honsing is a scheme for tracking normed conses that can be used only
; in Clozure Common Lisp (CCL).
;
; Static Honsing is an alternative to classic honsing that exploits static
; conses for greater efficiency.  Static conses are conses with several
; interesting properties: to each static cons there corresponds a unique
; natural number ``index''; it is possible to ``invert'' the index to retrieve
; the static cons; each static cons has a fixnum ``machine address.''  Static
; conses were implemented by Gary Byers and references to ``Gary'' below are to
; him.
;
; Here, only static conses can be considered normed, and SBITS is a bit-array
; that records which static conses are currently normed.  That is, suppose X is
; a static cons and let I be the index of X.  Then X is considered normed
; exactly when the Ith bit of SBITS is 1.  This is a very fast way to determine
; if a cons is normed!
;
;
; Addresses for Normed Objects.
;
; To support hons construction, we also need to be able to do the following:
; given two normed objects A and B, find the normed version of (A . B) or
; determine that none exists.
;
; Toward this goal, we first develop a reliable 'address' for every normed
; object; this address has nothing to do with machine (X86, PowerPC, or other)
; addresses.  To begin, we statically assign addresses to NIL, T, and certain
; small integers.  In particular (see also historic notes below):
;
;    Characters are given addresses 0-255, corresponding to their codes.
;    NIL and T are given addresses 256 and 257, respectively.
;    Integers in [-2^14, 2^23] are given the subsequent addresses
;    successively starting at -2^14 (address 258).
;
; All other objects are dynamically assigned addresses.  In particular, suppose
; that BASE is the start of the dynamically-allocated range.  Then,
;
;    The address of a static cons, C, is Index(C) + BASE, where Index(C) is the
;    index returned by HL-STATICP.
;
;    For any other atom, X, we construct an associated static cons, say X_C,
;    and then use Index(X_C) + BASE as the address of X.
;
; This scheme gives us a way to generate a unique, reliable address for every
; ACL2 Object we encounter.  These addresses start small and increase as more
; static conses are created.
;
; We record the association of these "other atoms" to their corresponding
; static conses in different ways, depending upon their types:
;
;   For symbols, the static cons is stored in the 'hl-static-address property
;   for the symbol.  This results in something a little bizarre: symbol
;   addresses are implicitly shared across all Hons Spaces, and so we must take
;   care to ensure that our address-allocation code is thread safe.
;
;   For strings, the STR-HT binds each string X to the pair XC = (NX
;   . TRUE-ADDR), where NX is the normed version of X and XC is a static cons
;   whose address is TRUE-ADDR (see hl-hspace-norm-atom).
;
;   For any other atoms, the Hons Space includes OTHER-HT, an EQL hash table
;   that associates each atom X with X_C, the static cons for X.
;
; In the future, we might want to think about the size of BASE.  Gary might be
; be able to extend static cons indices so that they start well after 128,
; perhaps eliminating the need to add BASE when computing the addresses for
; static conses.  On the other hand, it's probably just a matter of who is
; doing the addition, and our current scheme gives us good control over the
; range.
;
;
; Address-Based Hashing.
;
; Given the addresses of two normed objects, A and B, the function
; hl-addr-combine generates a unique integer that can be used as a hash key.
;
; Each Hons Space includes ADDR-HT, an EQL hash table that associates these
; keys to the normed conses to which they correspond.  In other words, suppose
; C = (A . B) is a normed cons, and KEY is the key generated for the addresses
; of A and B.  Then ADDR-HT associates KEY to C.
;
; Hence, assuming A and B are normed, we can determine whether a normed cons of
; the form (A . B) exists by simply generating the proper KEY and then checking
; whether ADDR-HT includes an entry for this key.
;
; We maintain the invariant that SBITS and ADDR-HT must correspond as described
; above.  That is, if (aref SBITS idx) = 1 then idx is the index of a static
; cons that is a key of ADDR-HT; and if C is a key of ADDR-HT, then C is a
; static cons such that (aref SBITS idx) = 1, where idx is the index of C.

; Default Sizes.  The user can always call hl-hons-resize to get bigger tables,
; but we still want good defaults.  These sizes are used in the structures that
; follow.  We try to avoid using any size less than 100.  A hash table of size
; 100 is pretty small and should be cheap to allocate, and making a hash table
; under that size is possibly not a very sensible thing to do, as it may
; quickly require resizing, etc.

(defparameter *hl-hspace-str-ht-default-size*
  ;; Usually there aren't too many strings, so let's start out small and just
  ;; let this grow if the user happens to be using a lot of strings.
  1000)

(defparameter *hl-ctables-nil-ht-default-size*
  ;; Classic honsing, table for honses (a . b) where b is NIL.  We might see
  ;; relatively many of these conses because NIL often terminates list, so
  ;; start this off with a moderately large size.
  5000)

(defparameter *hl-ctables-cdr-ht-default-size*
  ;; Classic honsing, main table for almost all honses, so make it large.
  100000)

(defparameter *hl-ctables-cdr-ht-eql-default-size*
  ;; Classic honsing, table for honses (a . b) where b is, e.g., a character or
  ;; number.  Not very common, so don't make this too large to start with.
  1000)

(defparameter *hl-hspace-addr-ht-default-size*
  ;; Static honsing, main table for honses, needs to be large
  150000)

(defparameter *hl-hspace-sbits-default-size*
  ;; Static honsing sbits array; pretty cheap.  It seems pretty sensible to
  ;; just match the size of the address table, given how indices appear to be
  ;; generated for static conses (see hl-staticp), at least for CCL.  But we
  ;; believe everything would work correctly even if this were a tiny value
  ;; like 100.  For example, in hl-hspace-truly-static-honsp we do an explicit
  ;; bounds check before accessing sbits[i], and in hl-hspace-hons-normed we do
  ;; an explicit bounds check and call hl-hspace-grow-sbits if there isn't
  ;; enough room before setting sbits[i] = 1.
  *hl-hspace-addr-ht-default-size*)

(defparameter *hl-hspace-other-ht-default-size*
  ;; Static honsing addresses for unusual atoms, probably doesn't need to be
  ;; very large.
  1000)

(defparameter *hl-hspace-fal-ht-default-size*
  ;; Fast alists table, probably there aren't going to be many fast alists
  ;; floating around so this doesn't need to be too large.
  1000)

(defparameter *hl-hspace-persist-ht-default-size*
  ;; For persistent honses.  Hardly anyone ever uses these so let's not
  ;; allocate very many by default.
  100)

; Foreshadowing: We provide a means, hl-hspace-hons-clear, to wipe out all
; honses -- except the mechanism protects fast alists and any hons marked as
; ``persistent'' in the hl-hspace-persist-ht table.

#-static-hons
(defstruct hl-ctables

; CTABLES STRUCTURE.  This is only used in classic honsing.  We aggregate
; together the NIL-HT, CDR-HT, and CDR-HT-EQL fields so that we can clear them
; out all at once in hl-hspace-hons-clear, for Ctrl+C safety.

  (nil-ht     (hl-mht :test #'eql :size *hl-ctables-nil-ht-default-size*)
              :type hash-table)

  (cdr-ht     (hl-mht :test #'eq :size *hl-ctables-cdr-ht-default-size*)
              :type hash-table)

  (cdr-ht-eql (hl-mht :test #'eql :size *hl-ctables-cdr-ht-eql-default-size*)
              :type hash-table))

(defun hl-initialize-faltable-table (fal-ht-size)

; Create the initial TABLE for the FALTABLE.  See the Essay on Fast Alists,
; below, for more details.
;
; [Sol]: Note (Sol): The non-lock-free hashing algorithm in CCL [for keyword
; argument :lock-free = nil in make-hash-table; also see
; http://trac.clozure.com/ccl/wiki/Internals/LockFreeHashTables] seems to have
; some bad behavior when remhashes are mixed in with puthashes in certain
; patterns.  One of these is noted below by Jared in the "Truly disgusting
; hack" note.  Another is that when a table grows to the threshold where it
; should be resized, it is instead rehashed in place if it contains any deleted
; elements -- so if you grow up to 99% of capacity and then repeatedly insert
; and delete elements, you're likely to spend a lot of time rehashing without
; growing the table.
;
; [Jared]: Truly disgusting hack.  As of Clozure Common Lisp revision 14519, in
; the non lock-free version of 'remhash', there is a special case: deleting the
; last remaining element from a hash table triggers a linear walk of the hash
; table, where every element in the vector is overwritten with the
; free-hash-marker.  This is devastating when there is exactly one active fast
; alist: every "hons-acons" and "fast-alist-free" operation requires a linear
; walk over the TABLE.  This took me two whole days to figure out.  To ensure
; that nobody else is bitten by it, and that I am not bitten by it again, here
; I ensure that the TABLE always has at least one fast alist within it.  This
; alist is unreachable from any ordinary ACL2 code so it should be quite hard
; to free it.  BOZO: Jared thinks it would be reasonable to see if this problem
; is fixed in CCL, in which case this code could be simplified.

  (let ((table (hl-mht :test #'eq :size (max 100 fal-ht-size)

; In early 2019, Rob Sumners told us that Centaur was hitting an apparent bug
; in how CCL resizes :weak :key hash-tables with :lock-free nil.  He and the
; Centaur folks suggested, after he did some timing tests, that we work around
; that issue by using :lock-free t here.  Our own stress test (see the comment
; in mf-mht about an experiment in directory books/centaur/esim/tutorial/)
; showed about 1/2% slowdown with :lock-free t here.  On March 22, 2019, Rob
; Sumners followed up to request that :lock-free is once again (the default of)
; nil.  He let us know at that time that CCL has been stable for awhile and
; that there were issues when :lock-free t tables were stressed.  Thus, we no
; longer include :lock-free t for #+ccl.

                       :weak :key)))
    #+ccl
    ;; This isn't necessary with lock-free, but doesn't hurt.  Note that T is
    ;; always honsed, so sentinel is a valid fast-alist.  I give this a
    ;; sensible name since it can appear in the (fast-alist-summary).
    (let* ((entry       (cons t t))
           (sentinel-al (cons entry 'special-builtin-fal))
           (sentinel-ht (hl-mht :test #'eql)))
      (setf (gethash t sentinel-ht) entry)
      (setf (gethash sentinel-al table) sentinel-ht))
    table))

(defstruct hl-falslot

; FAST-ALIST CACHE SLOT.  See the Essay on Fast Alists, below, for more
; details.

  (key nil)                  ;; The alist being bound, or NIL for empty slots
  (val nil)                  ;; Its backing hash table
  (uniquep t :type boolean)  ;; Flag for memory consistency

; Invariant 1.  If KEY is non-nil, then it is a valid fast alist.
;
; Invariant 2.  If KEY is non-nil, VAL is the appropriate backing hash table
; for this KEY (i.e., it is not some old/stale hash table or some newer/updated
; hash table.)
;
; Invariant 3.  If UNIQUEP is true, then KEY is not bound in the main TABLE,
; i.e., it exists only in this slot.
;
; Invariant 4.  No slots ever have the same KEY unless it is NIL.

  )

(defstruct (hl-faltable (:constructor hl-faltable-init-raw))

; FAST-ALIST TABLE STRUCTURE.  See the Essay on Fast Alists, below, for more
; details.
;
; This is essentially just an association from alists to backing hash tables.
; We previously made the associations an EQ hash table for alists to their
; backing hash tables.  And logically, that's all the HL-FALTABLE is.
;
; But, as a tweak, we add a small cache in front.  This cache allows us to
; avoid hashing in the very common cases where we're growing up a new hash
; table or repeatedly doing lookups in just a couple of hash tables.  The cache
; consists of fields slot1 and slot2, together with a Boolean, eject1, that
; tells us whether to eject slot1 (as opposed to slot2) when making a new cache
; entry.
;
; BOZO consider using CCL weak "populations" to make the slots weak like the
; table.

  (slot1 (make-hl-falslot) :type hl-falslot)
  (slot2 (make-hl-falslot) :type hl-falslot)

  (eject1 nil :type boolean) ;; want to eject slot1 on cache miss?

  (table (hl-initialize-faltable-table *hl-hspace-fal-ht-default-size*)
         :type hash-table))

(defun hl-faltable-init (&key (size *hl-hspace-fal-ht-default-size*))
  (hl-faltable-init-raw :table (hl-initialize-faltable-table size)))

(defstruct (hl-hspace (:constructor hl-hspace-init-raw))

; HONS SPACE STRUCTURE.  See the above essays on hons spaces, classic honsing,
; and static honsing above to understand this structure.

  (str-ht     (hl-mht :test #'equal :size *hl-hspace-str-ht-default-size*)
              :type hash-table)

  ;; Classic Honsing

  #-static-hons
  (ctables     (make-hl-ctables)
               :type hl-ctables)

  ;; Static Honsing

  #+static-hons
  (addr-ht    (hl-mht :test #'eql :size *hl-hspace-addr-ht-default-size*)
              :type hash-table)

  #+static-hons
  (sbits      (make-array *hl-hspace-sbits-default-size*

; Note: GCL with #+static-hons grows this array in acl2-default-restart.  See
; the comment there.

                          :element-type 'bit :initial-element 0)
              :type (simple-array bit (*)))

  #+static-hons
  (other-ht   (hl-mht :test #'eql :size *hl-hspace-other-ht-default-size*)
              :type hash-table)

  ;; Address limits are discussed in the essay on ADDR-LIMIT, below.
  #+static-hons
  (addr-limit  *hl-hspace-addr-ht-default-size* :type fixnum)

  ;; Miscellaneous Fields.

  ;; NORM-CACHE is described in the Essay on Hl-hspace-norm, below.
  (norm-cache   (make-hl-cache) :type hl-cache)

  ;; FALTABLE is described in the Essay on Fast Alists.
  (faltable     (hl-faltable-init) :type hl-faltable)

  ;; PERSIST-HT is described in comments in hl-hspace-persistent-norm.
  (persist-ht   (hl-mht :test #'eq :size *hl-hspace-persist-ht-default-size*)
                :type hash-table)

  )

(defun hl-hspace-init (&key
                       (str-ht-size       *hl-hspace-str-ht-default-size*)
                       (nil-ht-size       *hl-ctables-nil-ht-default-size*)
                       (cdr-ht-size       *hl-ctables-cdr-ht-default-size*)
                       (cdr-ht-eql-size   *hl-ctables-cdr-ht-eql-default-size*)
                       (addr-ht-size      *hl-hspace-addr-ht-default-size*)
                       (sbits-size        *hl-hspace-sbits-default-size*)
                       (other-ht-size     *hl-hspace-other-ht-default-size*)
                       (fal-ht-size       *hl-hspace-fal-ht-default-size*)
                       (persist-ht-size   *hl-hspace-persist-ht-default-size*))

; (HL-HSPACE-INIT ...) --> Hons Space
;
; This is the proper constructor for hons spaces.  The arguments allow you to
; override the default sizes for the various tables, which may be useful if you
; have a good idea of what your application will need.
;
; Note that we enforce certain minimum sizes, just because it seems like
; smaller sizes wouldn't really be sensible.

  #+static-hons
  (declare (ignore nil-ht-size cdr-ht-size cdr-ht-eql-size))
  #+static-hons
  (hl-hspace-init-raw
   :str-ht           (hl-mht :test #'equal :size (max 100 str-ht-size))
   :addr-ht          (hl-mht :test #'eql   :size (max 100 addr-ht-size))
   :addr-limit       (let ((addr-limit (max 100 addr-ht-size)))
                       (or (typep addr-limit 'fixnum)
                          ;; There is no reason to supply a non-fixnum as
                          ;; addr-ht-size, since Gary Byers tells us (email,
                          ;; June 2014) that a hash-table size is always a
                          ;; fixnum in 64-bit CCL.
                           (error ":Addr-limit is ~s (but must be a fixnum)"
                                  addr-limit))
                       addr-limit)
   :other-ht         (hl-mht :test #'eql   :size (max 100 other-ht-size))
   :sbits            (make-array (max 100 sbits-size)
                                 :element-type 'bit
                                 :initial-element 0)
   :norm-cache       (make-hl-cache)
   :faltable         (hl-faltable-init :size fal-ht-size)
   :persist-ht       (hl-mht :test #'eq :size (max 100 persist-ht-size))
   )

  #-static-hons
  (declare (ignore addr-ht-size sbits-size other-ht-size))
  #-static-hons
  (hl-hspace-init-raw
   #-static-hons
   :str-ht           (hl-mht :test #'equal :size (max 100 str-ht-size))
   :ctables          (make-hl-ctables
                      :nil-ht (hl-mht :test #'eql
                                      :size (max 100 nil-ht-size))
                      :cdr-ht (hl-mht :test #'eq
                                      :size (max 100 cdr-ht-size))
                      :cdr-ht-eql (hl-mht :test #'eql
                                          :size (max 100 cdr-ht-eql-size)))
   :norm-cache       (make-hl-cache)
   :faltable         (hl-faltable-init :size
                                       ;; Max with 100 is already handled in
                                       ;; hl-initialize-faltable-table
                                       fal-ht-size)
   :persist-ht       (hl-mht :test #'eq :size (max 100 persist-ht-size))
   ))


; ESSAY ON FLEX ALISTS (Classic Honsing Only)
;
; Given certain restrictions, a 'flex alist' is similar to an EQL alist, except
; that it is converted into a hash table after reaching a certain size.
;
;   RESTRICTION 1.  A flex alist must be used according to the single threaded
;   discipline, i.e., if you extend a flex alist A to a new flex alist, then
;   you must no longer use A as a flex alist.
;
;   RESTRICTION 2.  A flex alist must never be extended twice with the same
;   key.  This ensures that the entry returned by flex-assoc is always EQ to
;   the unique entry which was inserted by flex-acons and permits trivial
;   optimizations during the conversion to hash tables.
;
; Flex alists may be either ordinary, nil-terminated alists or hash tables.
; The idea is to avoid creating hash tables until there are enough elements to
; warrant doing so.  That is, a flex alist starts out as an alist, but may be
; dynamically promoted to a hash table after a certain size is reached.
;
; The main use of flex alists is in the CDR-HT and CDR-HT-EQL fields of a
; hons space.
;
; [Jared]: I wonder if a larger threshold would be better.  It might be worth
; having slow honsp checks when alists are in the 20-100 range in exchange for
; lower memory usage.

(defmacro hl-flex-alist-maxed-out (x)

; (hl-flex-alist-maxed-out x) == (> (length x) 18) for proper lists.  It is
; inspired by the Milawa function len-over-250p.  Although it is ugly, it is
; faster than looping and counting.  It is also faster on short lists (all of
; length at most 19) than `(not (eq nil (nthcdr 18 ,x))).

  `(let ((4cdrs (cddddr ,x)))
     (and (consp 4cdrs)
          (let ((8cdrs  (cddddr 4cdrs)))
            (and (consp 8cdrs)
                 (let* ((12cdrs (cddddr 8cdrs)))
                   (and (consp 12cdrs)
                        (let* ((16cdrs (cddddr 12cdrs))
                               (18cdrs (cddr 16cdrs)))
                          (consp 18cdrs)))))))))

(defmacro hl-flex-assoc (key al)

; (hl-flex-assoc key al) returns the entry associated with key, or returns nil
; if key is not bound.  Note that the comparisons performed by flex-assoc are
; always done with EQL.

; The check (listp al) seems faster in CCL than checking for a hash-table and
; is, according to disassemble) a check that is equivalent to (typep al 'list).
; Compare:

;    ? (defun foo ()
;        (let ((ht (make-hash-table)))
;          (loop for i fixnum from 1 to 100000000
;                when (listp ht)
;                do (return t))))
;    FOO
;    ? (time$ (foo))
;    ; (FOO) took
;    ; 0.09 seconds realtime, 0.09 seconds runtime
;    ; (1,552 bytes allocated).
;    NIL
;    ? (defun foo ()
;        (let ((ht '(3)))
;          (loop for i fixnum from 1 to 100000000
;                when (typep ht 'hash-table)
;                do (return t))))
;    FOO
;    ? (time$ (foo))
;    ; (FOO) took
;    ; 0.47 seconds realtime, 0.47 seconds runtime
;    ; (0 bytes allocated).
;    NIL
;    ?

  `(let ((key ,key)
         (al ,al))
     (if (listp al)
         (assoc key al)
       (gethash key (the hash-table al)))))

(defmacro hl-flex-acons (elem al &optional shared)

; (hl-flex-acons elem al) assumes that elem is a (key . val) pair, and extends
; the flex alist al by binding key to elem.
;
; WARNING: the caller must be sure to obey the restrictions described in the
; Essay on Flex Alists.  These are not enforced but their violation can lead to
; incorrect code!
;
; Note about Ctrl+C Safety: this is locally safe assuming that (setf (gethash
; ...)) is safe.  In the alist case we're pure, so there aren't any problems.
; In the 'conversion' case, the hash table doesn't become visible to the caller
; unless it's been fully constructed, so we're ok.  In the hash table case,
; we're a single setf, which we assume is okay.

  `(let ((elem ,elem)
         (al ,al)
         (shared ,shared))
     (cond
      ((listp al)
       (cond ((hl-flex-alist-maxed-out al)
              ;; Because of uniqueness, we don't need to worry about shadowed
              ;; pairs; we can just copy all pairs into the new hash table.
              (let ((ht (cond (shared

; In CCL, the default is for hash tables to be shared.  So we let CCL handle
; :shared and :lock-free.

                               (hl-mht :shared :default))
                              (t (hl-mht)))))
                (declare (type hash-table ht))
                (loop for pair in al do
                      (setf (gethash (car pair) ht) pair))
                (setf (gethash (car elem) ht) elem)
                ht))
             (t
              (cons elem al))))
      (t
       (setf (gethash (car elem) (the hash-table al))
             elem)
       al))))


; ----------------------------------------------------------------------
;
;                   DETERMINING IF OBJECTS ARE NORMED
;
; ----------------------------------------------------------------------

#+static-hons
(declaim (inline hl-hspace-truly-static-honsp))

#+static-hons
(defun hl-hspace-truly-static-honsp (x hs)

; (HL-HSPACE-TRULY-STATIC-HONSP X HS) --> BOOL
;
; Static Honsing only.  X must be an ACL2 Cons and HS must be a Hons Space.  We
; determine if X is a static cons whose bit is set in the SBITS array.  If so,
; X is considered normed with respect to HS.

  (let* ((idx (hl-staticp x)))
    (and idx
         (let ((sbits (hl-hspace-sbits hs)))
           (declare (type (simple-array bit (*)) sbits)) ; perhaps unnecessary
           (and (< (the fixnum idx) (the fixnum (length sbits)))
                (= 1 (the fixnum (aref sbits (the fixnum idx)))))))))

#-static-hons
(defmacro hl-hspace-find-flex-alist-for-cdr (b ctables)

; (HL-HSPACE-FIND-FLEX-ALIST-FOR-CDR B CTABLES) --> FLEX ALIST
;
; Classic Honsing only.  B is any ACL2 Object and CTABLES is the ctables
; structure from a Hons Space.  We return the flex alist that an ACL2 Object X
; = (A . B), for some A, must belong to for classic honsing.  Note that even
; though the NIL-HT starts out as a hash table, we can still regard it as a
; flex alist.

  `(let ((b ,b)
         (ctables ,ctables))
     (cond ((null b)
            (hl-ctables-nil-ht ctables))
           ((or (consp b)
                (symbolp b)
                (stringp b))
            (gethash b (hl-ctables-cdr-ht ctables)))
           (t
            (gethash b (hl-ctables-cdr-ht-eql ctables))))))

(declaim (inline hl-hspace-honsp))
(defun hl-hspace-honsp (x hs)

; (HL-HSPACE-HONSP X HS) --> BOOL
;
; X must be an ACL2 Cons and HS is a Hons Space.  We determine if X is normed
; with respect to HS.

  #+static-hons
  (hl-hspace-truly-static-honsp x hs)
  #-static-hons
  (let* ((a        (car x))
         (b        (cdr x))
         (ctables  (hl-hspace-ctables hs))
         (hons-set (hl-hspace-find-flex-alist-for-cdr b ctables))
         (entry    (hl-flex-assoc a hons-set)))
    (eq x entry)))

(defun hl-hspace-honsp-wrapper (x)
  ;; Bootstrapping hack for serialize
  ;; Assumes *default-hs* is already initialized
  (declare (special *default-hs*))
  (hl-hspace-honsp x *default-hs*))

(defun hl-hspace-faltable-wrapper ()
  ;; Bootstrapping hack for serialize
  ;; Assumes *default-hs* is already initialized
  (declare (special *default-hs*))
  (hl-hspace-faltable *default-hs*))

(defun hl-hspace-normedp (x hs)

; (HL-HSPACE-NORMEDP X HS) --> BOOL
;
; X may be any ACL2 Object and HS is a Hons Space.  We determine if X is normed
; with respect to HS.

  (declare (type hl-hspace hs))
  (cond ((consp x)
         (hl-hspace-honsp x hs))
        ((stringp x)
         (let* ((str-ht (hl-hspace-str-ht hs))
                (entry  (gethash x str-ht)))
           (and entry
                #+static-hons
                (eq x (car entry)) ; entry = (<normed x> . <true addr>)
                #-static-hons
                (eq x entry))))
        (t
         t)))

(defun hl-hspace-normedp-wrapper (x)
  ;; Bootstrapping hack for serialize
  ;; Assumes *default-hs* is already initialized
  (declare (special *default-hs*))
  (hl-hspace-normedp x *default-hs*))


; ----------------------------------------------------------------------
;
;                   EXTENDED EQUALITY OPERATIONS
;
; ----------------------------------------------------------------------

(defun hl-hspace-hons-equal-lite (x y hs)

; (HL-HSPACE-HONS-EQUAL-LITE X Y HS) --> BOOL
;
; X and Y may be any ACL2 Objects and HS must be a Hons Space.  We compute
; (EQUAL X Y).  If X and Y happen to be normed conses, we can settle the
; question of their equality via simple pointer equality; otherwise we just
; call (EQUAL X Y).

  (declare (type hl-hspace hs))
  (cond ((eq x y)
         t)
        ((and (consp x)
              (consp y)
              (hl-hspace-honsp x hs)
              (hl-hspace-honsp y hs))
         nil)
        (t
         (equal x y))))

(defun hl-hspace-hons-equal-1 (x y hs)

; This is just hl-hspace-hons-equal, except that we require x to be normed and
; we optimize under that assumption.

  (declare (type hl-hspace hs))
  (cond ((eq x y)
         t)
        ((consp x)
         (and (consp y)
              (not (hl-hspace-honsp y hs))
              (hl-hspace-hons-equal-1 (car x) (car y) hs)
              (hl-hspace-hons-equal-1 (cdr x) (cdr y) hs)))
        ((consp y)
         nil)
        (t
         (equal x y))))

(defun hl-hspace-hons-equal (x y hs)

; (HL-HSPACE-HONS-EQUAL X Y HS) --> BOOL
;
; X and Y may be any ACL2 Objects and HS must be a Hons Space.  We recursively
; check (EQUAL X Y), using pointer equality to determine the equality of any
; normed subtrees.

  (declare (type hl-hspace hs))
  (cond ((eq x y)
         t)
        ((consp x)
         (and (consp y)
              (cond
               ((hl-hspace-honsp x hs)
                (cond
                 ((hl-hspace-honsp y hs)
                  nil)
                 (t (and (hl-hspace-hons-equal-1 (car x) (car y) hs)
                         (hl-hspace-hons-equal-1 (cdr x) (cdr y) hs)))))
               ((hl-hspace-honsp y hs)
                (and (hl-hspace-hons-equal-1 (car y) (car x) hs)
                     (hl-hspace-hons-equal-1 (cdr y) (cdr x) hs)))
               (t (and (hl-hspace-hons-equal (car x) (car y) hs)
                       (hl-hspace-hons-equal (cdr x) (cdr y) hs))))))
        ((consp y)
         nil)
        (t
         (equal x y))))


; ----------------------------------------------------------------------
;
;                       STATIC HONS ADDRESSING
;
; ----------------------------------------------------------------------

; Our hashing scheme (see hl-addr-combine) performs best when both addresses
; involved are under 2^30.  In other words, there are about 1,073 million
; "fast-hashing" addresses and the rest are "slow-hashing".
;
; Historic notes.
;
; We did not originally statically assign addresses to the characters, and do
; not think it is particularly important to do so.  But, we like the idea of
; using numbers besides 0 and 1 as the addresses for T and NIL, under the
; probably misguided and certainly untested theory that perhaps using larger
; numbers will result in a better hashing distribution.
;
; We originally assigned a static, fast-hashing address for all integers in
; [-2^24, 2^24], and this decision "used up" about 33.6 million or 1/32 of the
; available fast-hashing addresses.  We later decided that this seemed slightly
; excessive, and we scaled the range down to [-2^14, 2^23].  This new scheme
; uses up 8.4 million or 1/128 of the fast-hashing addresses.  As a picture, we
; have:
;
;    8m                                                  1.07 bn
;   -|------------------------------- ... -----------------|--------------- ...
;   ^          dynamic fast-hashing                          slow-hashing
;   |
;   |
;  static fast-hashing
;
; We think this change is pretty much irrelevant and you shouldn't spend your
; time thinking about how to improve it.  Why?
;
;   (1) For most reasonable computations, slow addresses are never even used
;       and so this change won't matter at all.
;
;   (2) On the other hand, imagine a really massive computation that needs,
;       say, 2 billion normed conses.  Here, we are already paying the price of
;       slow addresses for half the conses.  Our change might mean that 1.06
;       billion instead of 1.04 billion of these conses will have fast-hashing
;       addresses, but this is only about 1% of the conses, so its effect on
;       performance is likely minimal.
;
; Even for applications that just barely exceed the boundary of slow-hashing,
; we're only talking about whether a small percentage of the conses have fast-
; or slow-hashing addresses.

#+static-hons
(defconstant hl-minimum-static-int
  ;; Minimum "small integer" that has a statically determined address.
  (- (expt 2 14)))

#+static-hons
(defconstant hl-maximum-static-int
  ;; Maximum "small integer" that has a statically determined address.
  (expt 2 23))

#+static-hons
(defconstant hl-num-static-ints
  ;; Total number of statically determined addresses needed for small integers.
  (1+ (- hl-maximum-static-int hl-minimum-static-int)))

#+static-hons
(defconstant hl-dynamic-base-addr
  ;; Total number of statically determined addresses for all atoms.  This is
  ;; the sum of:
  ;;  - 256 characters
  ;;  - 2 special symbols (T and NIL)
  ;;  - The number of statically determined integers
  (+ 256 2 hl-num-static-ints))

#+static-hons
(defconstant hl-static-int-shift
  ;; For integers with static addresses, the address is computed by adding
  ;; static-int-shift to their value.  These integers are in [min, max] where
  ;; min < 0 and max > 0.  The min integer will be assigned to location 258 =
  ;; 256 characters + 2 special symbols.  We then count up from there.
  (+ 256 2 (- hl-minimum-static-int)))

#+(and static-hons ccl)
(ccl::defstatic *hl-symbol-addr-lock*
                ;; lock for hl-symbol-addr; see below.
                (ccl::make-lock '*hl-symbol-addr-lock*))

#+static-hons
(defmacro hl-with-lock-grabbed (lock-form &rest args)
  #+ccl `(ccl::with-lock-grabbed ,lock-form ,@args)
  #+gcl (declare (ignore lock-form))
  #+gcl `(progn ,@args) ; GCL wart: We are assuming GCL is single-threaded.
  #-(or ccl gcl)
  #+gcl (declare (ignore lock-form args))
  #-(or ccl gcl)
  (error "~s is not implemented in this Lisp."
         'hl-with-lock-grabbed))

#+static-hons
(defmacro hl-symbol-addr (s)

; (HL-SYMBOL-ADDR S) --> NAT
;
; S must be a symbol other than T or NIL.  If it already has an address, we
; look it up and return it.  Otherwise, we must allocate an address for S and
; return it.
;
; We store the addresses of symbols on the symbol's property list.  This could
; cause problems in multi-threaded code if two threads were simultaneously
; trying to generate a 'hl-static-address entry for the same symbol.  In
; particular, each thread would generate its own static cons and try to use its
; index; the first thread, whose hash key would be overwritten by the second,
; would then be using the wrong address for the symbol.
;
; We could address this by using OTHER-HT instead of property lists, but
; property lists seem to be really fast, and our feeling is that we will really
; not be creating new addresses for symbols very often.  So, it's probably
; better to pay the price of locking in this very limited case.
;
; Notes about Ctrl+C Safety.  This function does not need to be protected by
; without-interrupts because installing the new 'hl-static-address cons is a
; single setf.

  `(let ((s ,s))
     (let ((addr-cons (get (the symbol s) 'hl-static-address)))
       (if addr-cons
           ;; Already have an address.  ADDR-CONS = (S . TRUE-ADDR), where
           ;; TRUE-ADDR is Index(ADDR-CONS) + BASE.  So, we just need to
           ;; return the TRUE-ADDR.
           (cdr addr-cons)
         ;; We need to assign an address.  Must lock!
         (hl-with-lock-grabbed
          (*hl-symbol-addr-lock*)
          ;; Some other thread might have assigned S an address before we
          ;; got the lock.  So, double-check and make sure that there still
          ;; isn't an address.
          (setq addr-cons (get (the symbol s) 'hl-static-address))
          (if addr-cons
              (cdr addr-cons)
            ;; Okay, safe to generate a new address.
            (let* ((new-addr-cons (hl-static-cons s nil))
                   (true-addr     (+ hl-dynamic-base-addr
                                     (hl-staticp new-addr-cons))))
              (rplacd (the cons new-addr-cons) true-addr)
              (setf (get (the symbol s) 'hl-static-address) new-addr-cons)
              true-addr)))))))

#+static-hons
(defun hl-addr-of-unusual-atom (x str-ht other-ht)

; Warning: Keep this in sync with pons-addr-of-argument.

; See hl-addr-of.  This function computes the address of any atom except for T
; and NIL.  Wrapping this in a function is mainly intended to avoid code blowup
; from inlining.

  (cond ((symbolp x)
         (hl-symbol-addr x))

        ((and (typep x 'fixnum)
              (<= hl-minimum-static-int (the fixnum x))
              (<= (the fixnum x) hl-maximum-static-int))
         (the fixnum
           (+ hl-static-int-shift (the fixnum x))))

        ((typep x 'array)

; The test above is equivalent to (stringp x), but twice as fast in CCL.  Note
; that (typep x 'vector) appears to be no faster.  More important, this
; function assumes that X is normed, so in particular, X is not a live stobj.

         ;; Since we assume X is normed, its entry in the STR-HT exists and has
         ;; the form XC = (NX . TRUE-ADDR), so we just need to return the
         ;; TRUE-ADDR.
         (cdr (gethash x str-ht)))

        ((characterp x)
         (char-code x))

        (t
         ;; Addresses for any other objects are stored in the OTHER-HT.  But
         ;; these objects do not necessarily have their addresses generated
         ;; yet.
         (let* ((entry (gethash x other-ht)))
           (if entry
               ;; ENTRY is a static cons that has the form (x . TRUE-ADDR)
               ;; where TRUE-ADDR is Index(ENTRY) + BASE.  So, we just need to
               ;; return the TRUE-ADDR.
               (cdr entry)
             ;; Else, we need to create an entry.
             (let* ((new-addr-cons (hl-static-cons x nil))
                    (true-addr     (+ hl-dynamic-base-addr
                                      (hl-staticp new-addr-cons))))
               (rplacd (the cons new-addr-cons) true-addr)
               (setf (gethash x other-ht) new-addr-cons)
               true-addr))))))

#+static-hons
(defmacro hl-addr-of (x str-ht other-ht)

; Warning: Keep this in sync with pons-addr-of-argument.

; (HL-ADDR-OF X STR-HT OTHER-HT) --> NAT and destructively updates OTHER-HT
;
; X is any normed ACL2 Object, and STR-HT and OTHER-HT are the corresponding
; fields of a Hons Space.  We determine and return the address of X.  This may
; require us to assign an address to X, which may require us to update the Hons
; Space.
;
; Ctrl+C Safety: this function need not be protected by without-interrupts.
; Even though it may modify the hons space, all invariants are preserved by the
; update; the only change is that OTHER-HT may be extended with a new entry,
; but the new entry is already valid by the time it is installed.

  `(let ((x ,x))
     (cond ((consp x)
            (+ hl-dynamic-base-addr (hl-staticp x)))
           ((eq x nil) 256)
           ((eq x t)   257)
           (t
            (hl-addr-of-unusual-atom x ,str-ht ,other-ht)))))

#+static-hons
(defun hl-nat-combine* (a b)
  ;; See community book books/system/hl-addr-combine.lisp for all documentation
  ;; and a proof that function hl-nat-combine, defined in that book, is
  ;; one-to-one.  At one point, this was going to be an inlined version of
  ;; hl-nat-combine.  We later decided not to inline it, since it's a rare case
  ;; and slow anyway, to avoid excessive expansion in hl-addr-combine*.
  (+ (let* ((a+b   (+ a b))
            (a+b+1 (+ 1 a+b)))
       (if (= (logand a+b 1) 0)
           (* (ash a+b -1) a+b+1)
         (* a+b (ash a+b+1 -1))))
     b))

#+static-hons
(defmacro hl-addr-combine* (a b)
  ;; Inlined version of hl-addr-combine, defined in community book
  ;; books/system/hl-addr-combine.lisp.  See that book for all documentation
  ;; and a proof that this function is one-to-one.  The only change we make
  ;; here is to use typep to see if the arguments are fixnums in the
  ;; comparisons, which speeds up our test loop by about 1/3.
  `(let ((a ,a)
         (b ,b))
     (if (and (typep a 'fixnum)
              (typep b 'fixnum)
              (< (the fixnum a) 1073741824) ; (expt 2 30)
              (< (the fixnum b) 1073741824))
         ;; Optimized version of the small case
         (the (signed-byte 61)
              (- (the (signed-byte 61)
                      (logior (the (signed-byte 61)
                                   (ash (the (signed-byte 31) a) 30))
                              (the (signed-byte 31) b)))))
       ;; Large case.
       (- (hl-nat-combine* a b)
          576460752840294399)))) ; (+ (expt 2 59) (expt 2 29) -1)


; ----------------------------------------------------------------------
;
;                            ADDR LIMIT
;
; ----------------------------------------------------------------------

; ESSAY ON ADDR-LIMIT (Static Honsing Only)
;
; This is a new feature that Jared added in January 2012.
;
; The ADDR-HT can grow very large.  For example, as an experiment I made an
; ADDR-HT with room for 100 million honses and filled it up to 99% full.  The
; total space it used was about 3.8 GB: 1.6 GB of actual cons data and 2.2 GB
; of overhead just for the table itself.  In some of our proofs, we allocate an
; address table with room for 500 million entries.  In this case, the size of
; the hash table's array (i.e., not counting the conses) would be 11 GB.
;
; Because of this, resizing the ADDR-HT can be very damaging.  What do I mean
; by this?  Note that resizing a hash table generally involves:
;
;   (1) Allocating a new hash table that is bigger
;   (2) Moving elements from the old hash table into the new hash table
;   (3) Freeing the old hash table (immediately or later via GC)
;
; Until step 3 completes, we need to simultaneously have both the old and new
; tables allocated.  But if the old table is already 11 GB, and we try to
; allocate a new table with 1.5x more space, the new table will be 16.5 GB and
; we'll need a total of 27.5 GB just for these tables.
;
; Practically, grabbing this much memory at once can be a problem.  If we're in
; the middle of a big proof and we have giant memoization tables laying around,
; we might already be running close to the max physical memory of the machine.
; In this situation, trying to grab another 16.5 GB just because we want one
; more HONS is probably a terrible idea.  It could cause us to start swapping,
; etc.  But as a Common Lisp hash table, the ADDR-HT will be resized when the
; Lisp decides, and there's not really anything we can do about it.
;
; The ADDR-LIMIT is an attempt to avoid this kind of trouble.  The basic idea
; is that shortly before resizing the ADDR-HT, we will call the function
; HL-ADDR-LIMIT-ACTION, which will inspect the ADDR-HT table and see if it's
; big enough to warrant doing anything drastic before the resize.  If it is big
; enough, we will do a CLEAR-MEMOIZE-TABLES and a HONS-WASH, which can throw
; away the hash table before growing it.  (But we will be able to restore the
; ADDR-HT from the SBITS array using HL-STATIC-INVERSE-CONS; see
; HL-REBUILD-ADDR-HT.)
;
; A practical difficulty of implementing this scheme is that Common Lisp
; doesn't give us a pre-resize hook for a hash table.  Instead, we have to keep
; track of how full the ADDR-HT is to decide when to call HL-ADDR-LIMIT-ACTION.
; We just add a counter, ADDR-LIMIT, for this purpose.  The idea is that this
; counter gets decreased every time we add a HONS into the ADDR-HT, and when it
; reaches zero we will trigger the action.
;
; The ADDR-LIMIT itself should be regarded merely as a performance counter and
; we generally do not make any claims about its accuracy or relevance to
; anything.  We insist that it is a fixnum for performance, and this should
; cause no soundness issues in practice.

#+static-hons
(defparameter *hl-addr-limit-minimum*
  ;; We don't do anything drastic during the HL-ADDR-LIMIT-ACTION unless the
  ;; ADDR-HT has grown at least this big.  At 50 million entries, we're
  ;; starting to get up into the gigabyte range on our allocations.  [Why
  ;; "gigabyte range"?  Recall that the ADDR-HT associates a key to a static
  ;; cons.  The key is presumably 8 bytes.  The cons is presumably stored as
  ;; two addresses in memory, which is 16 bytes.  So that's 24 bytes time 50
  ;; million, or 1200 million bytes, not including the hash table structure
  ;; itself, which however might be laid out flat and hence already be
  ;; accounted for.  So that's 1.2 GB.]
  50000000)

#+static-hons
(defun hl-make-addr-limit-current (hs)
  (declare (type hl-hspace hs))

; Reset the ADDR-LIMIT so that it will reach zero shortly after the table
; becomes 99% full.

  (let* ((addr-ht (hl-hspace-addr-ht hs))
         (count (hash-table-count addr-ht))
         (size
          ;; This is a fixnum -- important for the setting of
          ;; hl-hspace-addr-limit below -- as Gary Byers tells us (email, June
          ;; 2014) that a hash-table size is always a fixnum in 64-bit CCL.
          (hash-table-size addr-ht))
         (cutoff  (floor (* 0.995 (coerce size 'float)))))
    (setf (hl-hspace-addr-limit hs) (- cutoff count))))

#+static-hons
(defun hl-make-addr-limit-next (hs)
  (declare (type hl-hspace hs))

; Reset the ADDR-LIMIT so that it will reach zero shortly after the table is
; resized and then grows to 99% full.  Given reasonable rehashing sizes, this
; seems reasonably likely to trigger after one resize but before two resizes.
; At that point, HL-ADDR-LIMIT-ACTION will be able to do a better job of fixing
; it up again.

  (let* ((addr-ht       (hl-hspace-addr-ht hs))
         (count         (hash-table-count addr-ht))
         (size          (hash-table-size addr-ht))
         (rehash-size   (hash-table-rehash-size addr-ht))
         (future-cutoff (floor (* 0.995 rehash-size size))))
    (setf (hl-hspace-addr-limit hs)
          ;; Presumably the rehash-size is a fixnum, as required for the
          ;; hl-hspace-addr-limit hs); see the comment about fixnums in
          ;; hl-make-addr-limit-current.
          (- future-cutoff count))))

#+static-hons
(defun hl-addr-ht-fullness (hs)
  (let* ((addr-ht  (hl-hspace-addr-ht hs))
         (size     (hash-table-size addr-ht))
         (count    (hash-table-count addr-ht)))
    (/ (coerce count 'float) (coerce size 'float))))

(defparameter *hl-addr-limit-should-clear-memo-tables*
  ;; Not sure if this is a good idea or not.
  t)

#+static-hons
(defun hl-addr-limit-action (hs)

; (HL-ADDR-LIMIT-ACTION HS) --> NIL and destructively modifies HS
;   ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;   ** callers should not have ADDR-HT or SBITS let-bound!
;
; See the Essay on ADDR-LIMIT.  We see if the ADDR-HT is large and almost full,
; and if so we may clear the memoization tables and trigger a wash.  For the
; wash to work properly, callers of this function must not have ADDR-HT bound.
; This is especially important since the ADDR-HT of the new HS may be a new
; hash table, i.e., the old ADDR-HT is not relevant anymore.

  (declare (type hl-hspace hs))

  (unless (> (hl-addr-ht-fullness hs) 0.99)
    ;; This is a sort of safety mechanism to ensure that we only take
    ;; corrective action when we're over 99% full.  This means we don't have to
    ;; really work very hard to keep the ADDR-LIMIT accurate, it'll
    ;; automatically get bumped up if we trigger it too soon.
    (hl-make-addr-limit-current hs)
    (return-from hl-addr-limit-action nil))

  (let ((note-stream (get-output-stream-from-channel *standard-co*)))
    ;; We might eventually take this message out, but it seems nice to be able to
    ;; know that the ADDR-HT is about to be resized.
    (format note-stream "; Hons-Note: ADDR-LIMIT reached, ~:D used of ~:D slots.~%"
            (hash-table-count (hl-hspace-addr-ht hs))
            (hash-table-size (hl-hspace-addr-ht hs)))
    (force-output note-stream)

    (unless (> (hash-table-size (hl-hspace-addr-ht hs)) *hl-addr-limit-minimum*)
      ;; The table is small so it's not worth doing anything.  So, just bump up
      ;; the ADDR-LIMIT so we won't look at it again until the next resize.
      (hl-make-addr-limit-next hs)
      (return-from hl-addr-limit-action nil))

    ;; 99% full and the table is huge.  Do something drastic.
    (format note-stream "; Hons-Note: Trying to reclaim space to avoid ADDR-HT resizing...~%")
    (force-output note-stream)

    (when *hl-addr-limit-should-clear-memo-tables*
      (clear-memoize-tables))

    (time$ (hl-hspace-hons-wash hs)
           :msg "; Hons-wash: ~st sec, ~sa bytes~%")

    (format note-stream "; Hons-Note: After ADDR-LIMIT actions, ~:D used of ~:D slots.~%"
            (hash-table-count (hl-hspace-addr-ht hs))
            (hash-table-size (hl-hspace-addr-ht hs)))
    (force-output note-stream)

    nil))



; ----------------------------------------------------------------------
;
;                         HONS CONSTRUCTION
;
; ----------------------------------------------------------------------

#+static-hons
(defun hl-hspace-grow-sbits (idx hs)

; (HL-HSPACE-GROW-SBITS IDX HS) destructively updates HS
;   ** may install a new SBITS
;   ** callers should not have SBITS let-bound!
;
; Static Honsing only.  IDX must be a natural number and HS must be a Hons
; Space.  We generally expect this function to be called when SBITS has become
; too short to handle IDX, the static index of some static cons.  We copy SBITS
; into a new, larger array and install it into the Hons Space.
;
; Growing SBITS is slow because we need to (1) allocate a new, bigger array,
; and (2) copy the old contents of SBITS into this new array.  Accordingly, we
; want to add enough indices so that we can accommodate IDX and also any
; additional static conses that are generated in the near future without having
; to grow again.  But at the same time, we don't want to consume excessive
; amounts of memory by needlessly growing SBITS beyond what will be needed.  We
; try to balance these factors by increasing our capacity by 30% per growth.
;
;    BOZO -- consider different growth factors?
;
; Ctrl+C Safety.  This is locally ctrl+c safe assuming (setf (hl-hspace-bits
; hs) ...) is, because we only install the new array into the HS at the very
; end, and the new array is already valid by that time.  But if we change this
; to use some kind of array resizing, we might need to add without-interrupts.

  (declare (type hl-hspace hs))
  (let* ((sbits     (hl-hspace-sbits hs))
         (curr-len  (length sbits))
         (want-len  (floor (* 1.3 (max curr-len idx))))
         (new-len   (min (1- array-total-size-limit) want-len)))
    (when (<= new-len curr-len)
      (error "Unable to grow static hons bit array."))
    ;; CHANGE -- added a growth message
    (time$ (let ((new-sbits (make-array new-len
                                        :element-type 'bit
                                        :initial-element 0)))
             (declare (type (simple-array bit (*)) new-sbits))
             (loop for i fixnum below curr-len do
                   (setf (aref new-sbits i) (aref sbits i)))
             (setf (hl-hspace-sbits hs) new-sbits))
           :msg "; Hons-Note: grew SBITS to ~x0; ~st seconds, ~sa bytes.~%"
           :args (list new-len))))

(defun hl-hspace-norm-atom (x hs)

; (HL-HSPACE-NORM-ATOM X HS) --> X' and destructively updates HS.
;
; X is any ACL2 Atom and HS is a Hons Space.  We produce a normed version of X,
; extending the Hons Space if necessary.
;
; Ctrl+C Safety.  This function does not need to be protected with
; without-interrupts; even though it extends the STR-HT, the invariants on a
; Hons Space still hold after the update.

  (cond
   ((typep x 'array) ; <-- (stringp x)
    (let* ((str-ht (hl-hspace-str-ht hs))
           (entry  (gethash x str-ht)))

      #-static-hons
      ;; In classic honsing, STR-HT just associates strings to their normed
      ;; versions.  We make X the normed version of itself.
      (or entry
          (setf (gethash x str-ht) x))

      #+static-hons
      ;; In static honsing, STR-HT associates X with XC = (NX . TRUE-ADDR),
      ;; where NX is the normed version of X and TRUE-ADDR = Index(XC) + Base.
      (if entry
          (car entry)
        (let* ((new-addr-cons (hl-static-cons x nil))
               (true-addr     (+ hl-dynamic-base-addr
                                 (hl-staticp new-addr-cons))))
          (rplacd (the cons new-addr-cons) true-addr)
          (setf (gethash x str-ht) new-addr-cons)
          x))))

   (t
    ;; All other atoms are already normed.
    x)))

(defun hl-hspace-hons-normed (a b hint hs)

; (HL-HSPACE-HONS-NORMED A B HINT HS) --> (A . B) and destructively updates HS.
;    ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;    ** callers should not have ADDR-HT or SBITS let-bound!
;
; A and B may be any normed ACL2 objects and HS is a hons space.  HINT is
; either NIL, meaning no hint, or is a cons.
;
; HINT might have nothing to do with anything.  But if HINT happens to be a
; cons of the form (A . B), by which we mean its car is literally EQ to A and
; its cdr is literally EQ to B, then we might decide to make HINT become the
; normed version of (A . B).  The whole notion of a hint is mainly useful when
; we are re-norming previously normed objects, and might allow us to sometimes
; avoid constructing new conses when a suitable cons already exists.
;
; We produce a normed CONS that is equal to (A . B), possibly extending HS.
; This is the fundamental operation for what used to be called 'hopying' or
; 'hons copying,' and which is now referred to as 'norming' ACL2 objects.
;
; Ctrl+C Safety.  This function makes minimal use of without-interrupts to
; ensure its safety, and need not be protected by the caller.

  #+static-hons
  ;; Static Honsing Version
  (let* ((str-ht   (hl-hspace-str-ht hs))
         (other-ht (hl-hspace-other-ht hs))
         (addr-ht  (hl-hspace-addr-ht hs))
         (addr-a   (hl-addr-of a str-ht other-ht))
         (addr-b   (hl-addr-of b str-ht other-ht))
         (key      (hl-addr-combine* addr-a addr-b))
         (entry    (gethash key addr-ht)))
    (or entry
        ;; Else, we are going to build and install a new HONS.  First, do our
        ;; addr-limit checking.
        (cond ((<= (decf (hl-hspace-addr-limit hs)) 0)
               ;; I don't want to make any assumptions about what
               ;; HL-ADDR-LIMIT-ACTION does, so after doing the cleanup let's
               ;; just recur and start over.  That way, if somehow the cleanup
               ;; ends up creating a HONS, we'll be sure we don't accidentally
               ;; install some competing hons.

               ;; NOTE: for the washing to be effective, we need to be sure to
               ;; release our binding of the addr-ht.
               (setq addr-ht nil)
               (hl-addr-limit-action hs)
               (hl-hspace-hons-normed a b hint hs))
              (t
               (let* ((hint-idx (and (consp hint)
                                     (eq (car hint) a)
                                     (eq (cdr hint) b)
                                     (hl-staticp hint)))
                      (pair     (if hint-idx
                                    ;; Safe to use hint.
                                    hint
                                  (hl-static-cons a b)))
                      (idx      (or hint-idx (hl-staticp pair)))
                      (sbits    (hl-hspace-sbits hs)))
                 ;; Make sure there are enough sbits.  Ctrl+C Safe.
                 (when (>= (the fixnum idx)
                           (the fixnum (length sbits)))
                   (hl-hspace-grow-sbits idx hs)
                   (setq sbits (hl-hspace-sbits hs)))
                 (without-interrupts
                  ;; Since we must simultaneously update SBITS and ADDR-HT, the
                  ;; installation of PAIR must be protected by without-interrupts.
                  (setf (aref sbits idx) 1)
                  (setf (gethash key addr-ht) pair))
                 pair)))))

  #-static-hons
  ;; Classic Honsing Version
  (let ((ctables (hl-hspace-ctables hs)))
    (if (eq b nil)
        (let* ((nil-ht (hl-ctables-nil-ht ctables))
               (entry  (gethash a nil-ht)))
          (or entry
              (let ((new-cons (if (and (consp hint)
                                       (eq (car hint) a)
                                       (eq (cdr hint) b))
                                  hint
                                (cons a b))))
                ;; Ctrl+C Safe since it's only a single setf.
                (setf (gethash a nil-ht) new-cons))))

      (let* ((main-table (if (or (consp b)
                                 (symbolp b)
                                 (typep b 'array)) ;; (stringp b)
                             (hl-ctables-cdr-ht ctables)
                           (hl-ctables-cdr-ht-eql ctables)))
             (flex-alist (gethash b main-table))
             (entry      (hl-flex-assoc a flex-alist)))
        (or entry
            (let* ((was-alistp     (listp flex-alist))
                   (new-cons       (if (and (consp hint)
                                            (eq (car hint) a)
                                            (eq (cdr hint) b))
                                       hint
                                     (cons a b)))
                   (new-flex-alist (hl-flex-acons new-cons flex-alist)))
              ;; Ctrl+C Safety is subtle here.  If was-alistp, then the above
              ;; hl-flex-acons was applicative and didn't alter the Hons Space.
              ;; We'll go ahead and install the new flex alist, but this
              ;; installation occurs as an single update to the Hons Space.
              (when was-alistp
                (setf (gethash b main-table) new-flex-alist))
              ;; Otherwise, the flex-acons was non-applicative, and the Hons
              ;; Space has already been safely extended, so everything's ok.
              new-cons))))))


; ESSAY ON HL-HSPACE-NORM
;
; (HL-HSPACE-NORM X HS) --> X' and destructively updates HS.
;    ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;    ** callers should not have ADDR-HT or SBITS let-bound!
;
; X is any ACL2 Object and might be normed or not; HS is a Hons Space.  We
; return an object that is EQUAL to X and is normed.  This may require us to
; destructively extend HS.
;
; This function is non-destructive with respect to X.  Because of this, we
; sometimes need to recons portions of X.  Why?
;
;   One reason is that in static honsing we may only regard static conses as
;   normed, so if X includes non-static conses we will need to produce static
;   versions of them.
;
;   Another scenario is as follows.  Suppose X is (A . B), where B is normed
;   but A is not normed, and further suppose that there exists some normed A'
;   which is EQUAL to A, but no normed X' that is equal to X.  Here, we cannot
;   simply extend HS to regard X as normed, because this would violate our
;   invariant that the car of any normed cons is also normed.  Instead, we must
;   construct a new cons whose car is A' and whose cdr is B, and then use this
;   new cons as X'.
;
; We memoize the norming process to some degree.  The NORM-CACHE field of the
; Hons Space is a Cache Table (see above) that associates some recently
; encountered conses with their normed versions.
;
; Historically, we used a hash table instead.  A basic problem with this was,
; when should the table be created?  We surely do not want to have to create a
; new hash table every time hons-copy is called -- after all, it's called twice
; in every call of hons!  On the other hand, we don't want to use a global hash
; table that never gets cleaned out, because such a table could grow very large
; over time.  Our first solution was to split norming into two functions.  An
; auxiliary function did all the work, and freely used a hash table without
; regard to how large it might grow.  Meanwhile, a top-level wrapper function
; examined the hash table after the auxiliary function was finished, and if the
; table had been resized, we threw it away and started over.
;
; Using a global Cache Table nicely solves this problem.  The Cache Table keeps
; a fixed size and automatically forgets elements.

(defmacro hl-hspace-norm-aux-consp (x cache hs)

; This is just the case of hl-hspace-norm-aux for which x is known to be a
; consp that is not normed.  X should be a symbol in order to avoid repeated
; evaluation of x.

  (assert ; avoid repeated evaluation
   (and (symbolp x)
        (symbolp cache)
        (symbolp hs)))
  (assert ; avoid capture
   (not (intersectp-eq '(present-p val a d x-prime)
                       (list x cache hs))))
  `(mv-let (present-p val)
           (hl-cache-get ,x ,cache)
           (if present-p
               val
             (let* ((a       (hl-hspace-norm-aux (car ,x) ,cache ,hs))
                    (d       (hl-hspace-norm-aux (cdr ,x) ,cache ,hs))
                    (x-prime (hl-hspace-hons-normed a d ,x ,hs)))
               (hl-cache-set ,x x-prime ,cache)
               x-prime))))

(defun hl-hspace-norm-aux (x cache hs)

; (HL-HSPACE-NORM-AUX X CACHE HS) --> X' and destructively modifies CACHE and HS.
;    ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;    ** callers should not have ADDR-HT or SBITS let-bound!
;
; X is an ACL2 Object to copy.  CACHE is the cache table from HS, and HS is the
; Hons Space we are updating.  We return the normed version of X.

  (declare (type hl-cache cache)
           (type hl-hspace hs))
  (cond ((atom x)
         (hl-hspace-norm-atom x hs))
        ((hl-hspace-honsp x hs)
         x)
        (t
         (hl-hspace-norm-aux-consp x cache hs))))

(declaim (inline hl-hspace-norm-expensive))
(defun hl-hspace-norm-expensive (x hs)

; (HL-HSPACE-NORM-EXPENSIVE X HS) --> X' and destructively modifies HS.
;    ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;    ** callers should not have ADDR-HT or SBITS let-bound!
;
; X is assumed to be not an atom and not a honsp.  Since we put this in a
; separate function, hl-hspace-norm can be inlined without resulting in too
; much code expansion.

  (let ((cache (hl-hspace-norm-cache hs)))
    (hl-hspace-norm-aux-consp x cache hs)))

(declaim (inline hl-hspace-norm))
(defun hl-hspace-norm (x hs)
  ;; See the essay on HL-HSPACE-NORM.
  (cond ((atom x)
         (hl-hspace-norm-atom x hs))
        ((hl-hspace-honsp x hs)
         x)
        (t
         (hl-hspace-norm-expensive x hs))))

(defun hl-hspace-persistent-norm (x hs)

; (HL-HSPACE-PERSISTENT-NORM X HS) --> X' and destructively updates HS.
;    ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;    ** callers should not have ADDR-HT or SBITS let-bound!
;
; X is any ACL2 object and HS is a Hons Space.  We produce a new object that is
; EQUAL to X and is normed, which may require us to destructively modify HS.
;
; This function is essentially like hl-hspace-norm, except that when X is a
; cons, we also bind X' to T in the PERSIST-HT field of the Hons Space.  This
; ensures that X' will be restored in hl-hspace-hons-clear, and also that it
; cannot be garbage collected during hl-hspace-hons-wash.
;
;    INVARIANT P1: Every key in PERSIST-HT is a normed cons.
;
; Ctrl+C Safety.  An interrupt might cause X' to not be added to PERSIST-HT,
; but that's fine and doesn't violate any invariants of the hons space.

  (let ((x (hl-hspace-norm x hs)))
    (when (consp x)
      (let ((persist-ht (hl-hspace-persist-ht hs)))
        (setf (gethash x persist-ht) t)))
    x))

(defmacro hl-hspace-hons (x y hs)

; (HL-HSPACE-HONS X Y HS) --> (X . Y) which is normed, and destructively
; updates HS.
;    ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;    ** callers should not have ADDR-HT or SBITS let-bound!
;
; X and Y may be any ACL2 Objects, whether normed or not, and HS must be a Hons
; Space.  We produce a new cons, (X . Y), destructively extend HS so that this
; new cons is considered normed, and return it.

  `(let ((x ,x)
         (y ,y)
         (hs ,hs))
     (declare (type hl-hspace hs))
     (hl-hspace-hons-normed (hl-hspace-norm x hs)
                            (hl-hspace-norm y hs)
                            nil hs)))


; ----------------------------------------------------------------------
;
;                             FAST ALISTS
;
; ----------------------------------------------------------------------

; ESSAY ON FAST ALISTS
;
; Prerequisite: see :doc fast-alists for a user-level overview of fast alists,
; which for instance introduces the crucial notion of discipline.
;
; The implementation of fast alists is actually fairly simple.  Each Hons Space
; includes a FALTABLE which associates each "fast alist" with an EQL hash
; table, called its "backing" hash table.
;
; INVARIANTS.  For every "fast alist" AL that is bound in the FALTABLE,
;
;    1. AL is non-empty, i.e., atoms are never bound in FALTABLE.
;
;    2. For every (KEY . VAL) pair in AL, KEY is normed.  This justifies our
;       use of EQL-based backing hash tables.
;
;    3. The backing hash table, HT, must "agree with" AL.  In particular, for
;       all ACL2 Objects, KEY, the following relation must be satisfied:
;
;        (equal (hons-assoc-equal KEY AL)
;               (gethash (hons-copy KEY) HT))
;
;       In other words, for every (KEY . VALUE) pair in AL, HT must associate
;       KEY to (KEY . VALUE).  Meanwhile, if KEY is not bound in AL, then it
;       must not be bound in HT.
;
; PREVIOUSLY we also insisted that each AL consists entirely of conses, i.e.,
; there are no "malformed" entries in the alist.  We abandoned this requirement
; to allow MAKE-FAST-ALIST to be the identity.
;
; The FALTABLE might as well have been an EQ hash table, and historically it
; was.  But this meant that each HONS-ACONS had to do:
;
;     - (GETHASH ALIST FALTABLE)                 find the current HT
;     - (REMHASH ALIST FALTABLE)                 disassociate HT from ALIST
;     - (SETF (GETHASH KEY HT) VAL)              update HT
;     - (SETF (GETHASH NEW-ALIST FALTABLE) HT)   associate HT with NEW-ALIST
;
; This takes a lot of FALTABLE updates (three for each hons-acons) and all of
; this hashing gets expensive.  To avoid it, we changed the FALTABLE into a
; structure which had a hash table and also a very small (two slot) cache in
; the front.  This cache lets us be working with up to two fast alists without
; having to hash to find the backing hash tables.


; ESSAY ON CTRL+C SAFETY FOR FAST ALISTS
;
; Ctrl+C safety is really difficult for fast alists.  The function
; hl-hspace-hons-acons provides the simplest example of the problem.  You might
; think that the PROGN in this function (and similarly, in
; hl-hspace-hons-acons!) should be a without-interrupts instead.  After all, an
; ill-timed interrupt by the user could cause us to remove the old hash table
; from FALTABLE without installing the new hash table, potentially leading to
; discipline failures even in otherwise perfectly disciplined user-level code.
;
; But the problem runs deeper than this.  Even if we used without-interrupts,
; it wouldn't be enough.  After all, an equally bad scenario is that we
; successfully install the new table into FALTABLE, but then are interrupted
; before ANS can be returned to the user's code.  It hardly matters that the
; hash table has been properly installed if they don't have the new handle to
; it.
;
; There really isn't any way for us, in the implementation of fast alists, to
; prevent interrupts from violating single-threaded discipline.  Consider for
; instance a sequence such as:
;
;   (defconst *foo* (make-fast-alist ...))
;   (defconst *bar* (do-something (hons-acons 0 t *foo*)))
;
; Here, if the user interrupts do-something at any time after the inner
; hons-acons has been executed, then the hash table for *foo* has already been
; extended and there's no practical way to maintain discipline.
;
; Because of this, we abandon the goal of trying to maintain discipline across
; interrupts, and set upon a much easier goal of ensuring that whatever hash
; tables happen to be in the FALTABLE are indeed accurate reflections of the
; alists that are bound to them.  This weaker criterion means that the progn
; below is adequate.

(defvar *defeat-slow-alist-action*

; Bind this to 'stolen to defeat the slow-alist-action only for stolen fast
; alists, and to t to defeat the slow-alist-action unconditionally.

  nil)

(defun get-slow-alist-action (stolen-p state)

; Stolen-p is t if we are determing the action on discovering a stolen
; fast-alist, and is nil otherwise (i.e., slow hons-get).

  (and (if stolen-p
           (not *defeat-slow-alist-action*)
         (not (eq *defeat-slow-alist-action* t)))
       (let* ((alist   (table-alist 'hons (w state)))
              (warning (hons-assoc-equal 'slow-alist-warning alist)))
         (and (consp warning)
              (cdr warning)))))

(defun hl-slow-alist-warning (name)

; Formerly, name is the name of the function wherein we noticed a problem.
; However, for the user's sake we typically print a user-friendly version of
; the name, such as HONS-GET rather than HL-HSPACE-HONS-GET.

  (let ((action (get-slow-alist-action nil *the-live-state*)))
    (when action
      (let* ((path (global-val 'include-book-path
                              (w *the-live-state*)))
             (book-string (if path
                              (concatenate
                               'string
                               "
This violation occurred while attempting to include the book:
"
                               (car path))
                            ""))
             (normal-string "
*****************************************************************
Fast alist discipline violated in ~a.
See :DOC slow-alist-warning to suppress or break on this warning.~a
*****************************************************************~%"))
        #-acl2-par
        (format *error-output* normal-string name book-string)
        #+acl2-par
        (let ((prover-par (and (f-get-global 'waterfall-parallelism *the-live-state*)
                               (f-get-global 'in-prove-flg *the-live-state*))))
          (cond ((or prover-par
                     (f-get-global 'parallel-execution-enabled *the-live-state*))
                 (format *error-output* "
*****************************************************************
Fast alist discipline violated in ~a.  (May be from
~aparallelism; see :DOC unsupported-~aparallelism-features.)
See :DOC slow-alist-warning to suppress or break on this warning.~a
*****************************************************************~%"
                         name
                         (if prover-par
                             "waterfall-"
                           "")
                         (if prover-par
                             "waterfall-"
                           "")
                         book-string))
                (t (format *error-output* normal-string name book-string)))))
      (when (eq action :break)
        (format *error-output* "
To avoid the following break and get only the above warning:~%  ~s~%"
                '(set-slow-alist-action :warning))
        (break$)))))

(defun hl-faltable-maphash (f faltable)
  (declare (type hl-faltable faltable))

; We assume F doesn't modify faltable or any of its slots.

  (let ((slot1 (hl-faltable-slot1 faltable))
        (slot2 (hl-faltable-slot2 faltable))
        (table (hl-faltable-table faltable)))

    ;; Silly, just to make sure we visit each thing only once, bring everything
    ;; into a unique state.
    (unless (hl-falslot-uniquep slot1)
      (remhash (hl-falslot-key slot1) table)
      (setf (hl-falslot-uniquep slot1) t))

    (unless (hl-falslot-uniquep slot2)
      (remhash (hl-falslot-key slot2) table)
      (setf (hl-falslot-uniquep slot2) t))

    (when (hl-falslot-key slot1)
      (funcall f (hl-falslot-key slot1) (hl-falslot-val slot1)))

    (when (hl-falslot-key slot2)
      (funcall f (hl-falslot-key slot2) (hl-falslot-val slot2)))

    (maphash f table)))

(defun hl-faltable-load-empty-slot (alist slot faltable)
  (declare (type hl-faltable faltable)
           (type hl-falslot slot))

; SLOT[key] must be NIL.
;
; We want to load up SLOT with ALIST and its backing hash table.  ALIST should
; be a cons and must not be bound in any other slot.  In the case of good
; discipline, the table lookup will succeed and we will get its hash table
; loaded into val.  In the case of bad discipline, both the key and val will
; become NIL.

  (let* ((table (hl-faltable-table faltable))
         (val   (gethash alist table)))
    (setf (hl-falslot-uniquep slot) nil)
    (setf (hl-falslot-val slot) val)
    (setf (hl-falslot-key slot)
          ;; Ensure KEY gets set to NIL in the case of bad discipline, so we
          ;; don't violate Invariant 1.
          (and val alist))
    (remhash alist table)
    (setf (hl-falslot-uniquep slot) t)))

(defun hl-faltable-eject (slot faltable)
  (declare (type hl-faltable faltable)
           (type hl-falslot slot))

; We want to remove any ALIST and VAL from SLOT, and move them back into the
; main table, to free up this slot.  We don't care whether SLOT is unique,
; because if it happens to be non-unique, we're going to be putting its value
; back into the table anyway.

  (let ((key (hl-falslot-key slot)))
    (when key
      (setf (hl-falslot-uniquep slot) nil)
      (setf (gethash key (hl-faltable-table faltable))
            (hl-falslot-val slot))
      (setf (hl-falslot-key slot) nil)
      (setf (hl-falslot-val slot) nil)
      (setf (hl-falslot-uniquep slot) t))))

(defun hl-faltable-get-free-slot (faltable)
  (declare (type hl-faltable faltable))

; Choose whichever slot was least recently used and eject it.  Returns an empty
; slot.  We assume that your goal is to put something into the slot, so we mark
; the OTHER slot as the one to eject.

  (let* ((eject1 (hl-faltable-eject1 faltable))
         (loser  (if eject1
                     (hl-faltable-slot1 faltable)
                   (hl-faltable-slot2 faltable))))
    (hl-faltable-eject loser faltable)
    (setf (hl-faltable-eject1 faltable) (not eject1))
    loser))

(defun hl-faltable-slot-lookup (alist faltable)
  (declare (type hl-faltable faltable))

; ALIST should be a cons.  Try to find ALIST only among the slots of FALTABLE.
; Returns a SLOT (which is guaranteed to be unique) or NIL.

  (let* ((slot1 (hl-faltable-slot1 faltable))
         (slot  (if (eq alist (hl-falslot-key slot1))
                    slot1
                  (let ((slot2 (hl-faltable-slot2 faltable)))
                    (if (eq alist (hl-falslot-key slot2))
                        slot2
                      nil)))))
    (unless slot
      (return-from hl-faltable-slot-lookup nil))

    (unless (hl-falslot-uniquep slot)
      ;; The slot may be duplicated in the table, so be sure to delete it and
      ;; then we can claim it is free.  This can happen if there are interrupts
      ;; at just the right time during hl-faltable-eject, etc.
      (remhash alist (hl-faltable-table faltable))
      (setf (hl-falslot-uniquep slot) t))

    (setf (hl-faltable-eject1 faltable) (not (eq slot slot1)))

    slot))

(defun hl-faltable-general-lookup (alist faltable)
  (declare (type hl-faltable faltable))

; ALIST should be a cons.  Try to find ALIST first among the slots of FALTABLE;
; otherwise, eject a slot, load it into a slot, and return the slot.  In any
; event, this just returns a slot that contains ALIST and is guaranteed to be
; unique.  If there is a discipline failure, an empty slot is returned (i.e.,
; its key and val are nil).

  (or (hl-faltable-slot-lookup alist faltable)
      (let ((slot (hl-faltable-get-free-slot faltable)))
        ;; The slot is empty, load it up.
        (hl-faltable-load-empty-slot alist slot faltable)
        slot)))

(defun hl-faltable-remove (alist faltable)
  (declare (type hl-faltable faltable))

; ALIST should be a cons.  Remove ALIST from the slots or table, wherever it
; may be.  We sort of optimize this so that if the alist isn't already in a
; slot, we don't ruin the slots.

  (let ((slot (hl-faltable-slot-lookup alist faltable)))
    (cond (slot
           ;; We know it's unique by the guarantee in hl-faltable-slot-lookup,
           ;; so we just need to empty this slot.
           (setf (hl-falslot-key slot) nil)
           (setf (hl-falslot-val slot) nil) ;; just a hint for gc
           ;; The slot-lookup set eject1 to the wrong thing since we're going
           ;; to delete this slot, so set it back to the right thing.
           (setf (hl-faltable-eject1 faltable)
                 (not (hl-faltable-eject1 faltable))))

          (t
           ;; No slot, so just remove it from the table; this works whether
           ;; it exists or not.
           (remhash alist (hl-faltable-table faltable))))))

(defun hl-hspace-fast-alist-free (alist hs)
  (declare (type hl-hspace hs))
  (cond ((atom alist)
         alist)
        (t
         (hl-faltable-remove alist (hl-hspace-faltable hs))
         alist)))

(defun hl-hspace-hons-get (key alist hs)

; (HL-HSPACE-HONS-GET KEY ALIST HS) --> ANS and destructively modifies HS
;   ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;   ** callers should not have ADDR-HT or SBITS let-bound!
;
; Fundamental fast alist lookup operation.  Norm the key (hence the possible
; modifications to the HS), then look it up in the backing hash table for the
; alist.

  (declare (type hl-hspace hs))
  (if (atom alist)
      nil
    (let* ((faltable (hl-hspace-faltable hs))
           (slot     (hl-faltable-general-lookup alist faltable))
           (val      (hl-falslot-val slot)))
      (if val
          ;; Good discipline, val is the hash table, so look up the key.
          ;; We have to hons the key to justify EQL hashing.
          (values (gethash (hl-hspace-norm key hs) val))
        ;; Bad discipline, val is just nil and hence is unusable, look
        ;; up the key slowly in the alist.
        (progn
          (hl-slow-alist-warning 'hons-get)
          (hons-assoc-equal key alist))))))

(defun hl-hspace-hons-acons (key value alist hs)

; (HL-HSPACE-HONS-ACONS KEY VALUE ALIST HS) --> ALIST' and destructively modifies HS.
;   ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;   ** callers should not have ADDR-HT or SBITS let-bound!
;
;  - KEY and VALUE are any ACL2 Objects, whether normed or not.
;
;  - ALIST is an ordinary ACL2 Object; for good discipline ALIST must have a
;    hash table supporting it in the FAL-HT.
;
;  - HS is the Hons Space whose FAL-HT and other fields may be destructively
;    updated.
;
; When ALIST is a natural number, we interpret it as a size hint that says how
; large the new hash table should be, but we impose a minimum of 60 elements.
; We always begin by honsing the key, which justifies our use of EQL hash
; tables.

  (declare (type hl-hspace hs))
  (let* (;; The key must always normed regardless of honsp.
         (key      (hl-hspace-norm key hs))
         (entry    (cons key value))
         (ans      (cons entry alist))
         (faltable (hl-hspace-faltable hs)))

    (if (atom alist)
        ;; New fast alist.  Try to use the size hint if one was provided.
        (let* ((size (if (and (typep alist 'fixnum)
                              (<= 60 (the fixnum alist)))
                         alist
                       60))
               (tab  (hl-mht :size size))
               (slot (hl-faltable-get-free-slot faltable)))
          (setf (gethash key (the hash-table tab)) entry)

          ;; We know the slot is empty and unique, just install the new
          ;; key/value pair.  We install the key last so that the slot
          ;; still looks empty for as long as possible.
          (setf (hl-falslot-val slot) tab)
          (setf (hl-falslot-key slot) ans))

      ;; Possibly existing fast alist.
      (let* ((slot (hl-faltable-general-lookup alist faltable))
             (val  (hl-falslot-val slot)))

; Warning: Do not change the following IF to a COND that eliminates the PROGN
; below, without updating the comment about that PROGN in the Essay ON Ctrl+C
; Safety for Fast Alists.

        (if (not val)
            ;; Discipline failure, no valid backing alist.
            (hl-slow-alist-warning 'hons-acons)
          (progn ; see warning above
            ;; We temporarily set the KEY to nil to break the old association
            ;; from ALIST to VAL.  Then, install the new entry into the VAL,
            ;; and finally set KEY to ANS so that the new association is
            ;; created.
            (setf (hl-falslot-key slot) nil)
            (setf (gethash key (the hash-table val)) entry)
            (setf (hl-falslot-key slot) ans)))))

    ans))


(defun hl-alist-stolen-warning (name)
  ;; Name is the name of the function wherein we noticed a problem.
  (let ((action (get-slow-alist-action t *the-live-state*)))
    (when (and action
               (not (eq *defeat-slow-alist-action* 'stolen)))
      (let ((path (global-val 'include-book-path
                              (w *the-live-state*))))
        (format *error-output* "
*****************************************************************
Fast alist stolen by ~a.
See the documentation for fast alists for how to fix the problem,
or suppress this warning message with:~%  ~a~a
****************************************************************~%"
                name
                '(set-slow-alist-action nil)
                (if path
                    (concatenate
                     'string
                     "
This violation occurred while attempting to include the book:
"
                     (car path))
                  "")))
      (when (eq action :break)
        (format *error-output* "
To avoid the following break and get only the above warning:~%  ~s~%"
                '(set-slow-alist-action :warning))
        (break$)))))

(defun hl-hspace-hons-acons! (key value alist hs)

; (HL-HSPACE-HONS-ACONS! KEY VALUE ALIST HS) --> ALIST' and destructively modifies HS.
;   ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;   ** callers should not have ADDR-HT or SBITS let-bound!
;
; Like HL-HSPACE-HONS-ACONS, except honses the ANS alist as well.  This is
; subtle because the ANS we create might already exist!

  (declare (type hl-hspace hs))
  (let* ((key      (hl-hspace-norm key hs))
         (entry    (hl-hspace-hons key value hs))
         (ans      (hl-hspace-hons entry alist hs))
         (faltable (hl-hspace-faltable hs)))

    (let ((slot (hl-faltable-general-lookup ans faltable)))
      (when (hl-falslot-key slot)
        ;; "Inadvertent" hash table stealing.  We now print a warning before
        ;; removing the old binding.
        (hl-alist-stolen-warning 'hons-acons!)
        ;; We could do something smart to reuse this alist, but this is a bad
        ;; case anyway and we don't really expect it to happen much.
        (setf (hl-falslot-key slot) nil)
        (setf (hl-falslot-val slot) nil)))

    (if (atom alist)
        ;; New fast alist.
        (let* ((size (if (and (typep alist 'fixnum)
                              (<= 60 (the fixnum alist)))
                         alist
                       60))
               (tab  (hl-mht :size size))
               (slot (hl-faltable-get-free-slot faltable)))
          (setf (gethash key (the hash-table tab)) entry)
          (setf (hl-falslot-val slot) tab)
          (setf (hl-falslot-key slot) ans))

      ;; Possibly existing fast alist.
      (let* ((slot (hl-faltable-general-lookup alist faltable))
             (val  (hl-falslot-val slot)))

; Warning: Do not change the following IF to a COND that eliminates the PROGN
; below, without updating the comment about that PROGN in the Essay ON Ctrl+C
; Safety for Fast Alists.

        (if (not val)
            (hl-slow-alist-warning 'hons-acons)
          (progn ; see warning above
            (setf (hl-falslot-key slot) nil)
            (setf (gethash key (the hash-table val)) entry)
            (setf (hl-falslot-key slot) ans)))))

    ans))

(defun hl-alist-longest-normed-tail (alist hs)

; (HL-ALIST-LONGEST-NORMED-TAIL ALIST HS) --> TAIL
;
; ALIST is an arbitrary ACL2 object.  This returns the longest tail of ALIST
; where all the keys are already normed.  This tail doesn't need to be reconsed
; when we go to make a fast version of ALIST.

  (declare (type hl-hspace hs))
  (let ((ok-tail alist))
    ;; ok-tail is a tail of alist on which we haven't yet found any unnormed keys.
    (loop for tail on alist while (consp tail) do
          (let ((pair (car tail)))
            ;; We can just skip over any non-conses since they don't contribute
            ;; to the alist.
            (when (and (consp pair)
                       (not (hl-hspace-normedp (car pair) hs)))
              (setq ok-tail (cdr tail)))))
    ok-tail))

(defun hl-make-fast-norm-keys (alist tail hs)

; (HL-MAKE-FAST-NORM-KEYS ALIST TAIL HS) --> ALIST' and destructively modifies HS.
;   ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;   ** callers should not have ADDR-HT or SBITS let-bound!
;
; ALIST is an arbitrary ACL2 object.  TAIL is its longest-normed-tail.  We
; construct a new ALIST that is EQUAL to ALIST, where all the keys are normed.

  (declare (type hl-hspace hs))
  (if (eq tail alist)
      alist

; The following algorithm is a bit subtle.  First-cons is an alist with a fresh
; spine whose cdr is EQUAL to an initial segment of alist, but not expected to
; be EQ because the keys of (cdr first-cons) are all normed.  Last-cons is the
; last cons in the list fresh-cons.  We extend first-cons on its end by
; destructively modifying last-cons as we walk through alist, replacing its cdr
; with a new last-cons of the form (cons fixed-pair nil).  We stop that walk as
; soon as we reach a tail whose keys are known to be normed already,
; destructively replacing the nil just above with that tail.  The result is
; then the cdr of fresh-cons, which has always been EQUAL to an initial segment
; of alist but is now EQUAL to alist itself because of the final replacement of
; (cdr last-cons) by tail.

    (let* ((first-cons (list nil))
           (last-cons first-cons))
      (loop for rest on alist
            while (and (consp rest) (not (eq rest tail)))
            do
            (let* ((pair (car rest))
                   (cons (list (if (and (consp pair)

; We avoid copying pair if its car is already normed.

                                        (not (hl-hspace-normedp (car pair)
                                                                hs)))
                                   (cons (hl-hspace-norm (car pair) hs)
                                         (cdr pair))
                                 pair))))
              (setf (cdr last-cons) cons)
              (setq last-cons cons)))
      (setf (cdr last-cons) tail)
      (cdr first-cons))))

(defun hl-make-fast-alist-put-pairs (alist ht)

; (HL-MAKE-FAST-ALIST-PUT-PAIRS ALIST HT) --> HT'.
;
; ALIST must have normed keys.  Assuming that HT starts empty, we initialize it
; to have the correct values for ALIST.  That is, we set HT[KEY] := VALUE for
; each (KEY . VALUE) pair in ALIST, except that we don't do this update when
; HT[KEY] is already bound, i.e., we properly skip shadowed pairs.

  (declare (type hash-table ht))
  (loop for rest on alist while (consp rest) do
        (let ((pair (car rest)))
          (when (and (consp pair)
                     (not (gethash (car pair) ht)))
            (setf (gethash (car pair) ht) pair)))))

(defun hl-hspace-make-fast-alist (alist hs)

; (HL-HSPACE-MAKE-FAST-ALIST ALIST HS) --> ALIST' and destructively modifies HS.
;   ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;   ** callers should not have ADDR-HT or SBITS let-bound!
;
; This function returns a fast ALIST' which is EQUAL to ALIST.  Ideally ALIST'
; can just be ALIST, but this is sometimes not possible when ALIST' has keys
; that are not normed.  If ALIST is already fast and already has a backing hash
; table, we just return it.  Otherwise we build a hash table for it.

  (declare (type hl-hspace hs))
  (if (atom alist)
      ;; Can't create a hash table for an atom, nothing to do.
      alist
    (let* ((faltable    (hl-hspace-faltable hs))
           (slot        (hl-faltable-general-lookup alist faltable))
           (alist-table (hl-falslot-val slot)))
      (if alist-table
          ;; Already has an associated hash table, nothing to do.
          alist
        (let* (;; Find the largest tail of alist in which all keys are normed.
               (tail (hl-alist-longest-normed-tail alist hs))
               ;; Makes a copy of alist in which all keys are normed.
               (alist (hl-make-fast-norm-keys alist tail hs)))
          ;; We need to make a new hash table to back ALIST.  As in
          ;; hl-hspace-fast-alist-fork, we choose a size of (max 60 (* 1/8
          ;; length)).
          (setq alist-table (hl-mht :size (max 60 (ash (len alist) -3))))
          (hl-make-fast-alist-put-pairs alist alist-table)
          ;; The slot is empty, so install everything.  Since the value wasn't
          ;; found, the initial ALIST isn't bound; if we ended up making a new
          ;; alist due to honsing any keys, it's also not bound because we used
          ;; cons.  So, uniqueness is guaranteed.  And we already know from the
          ;; general lookup that it is unique.
          (setf (hl-falslot-val slot) alist-table)
          (setf (hl-falslot-key slot) alist)
          alist)))))


; See :DOC fast-alist-fork for an introduction to that function, including
; its logical definition.  Here we provide support for its implementation.
;
; (HL-HSPACE-FAST-ALIST-FORK ALIST ANS HONSP HS) --> ANS' and destructively modifies HS.
;   ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;   ** callers should not have ADDR-HT or SBITS let-bound!
;
; ALIST is either a fast or slow alist, and ANS should be a fast alist.  HONSP
; says whether our extension of ANS' should be made with honses or conses.  HS
; is a Hons Space and will be destructively modified.

(defun hl-fast-alist-fork-aux-really-slow (alist ans honsp hs)
  ;; This is our function of last resort and we only call it if discipline has
  ;; failed.  We don't try to produce a fast alist, because there may not even
  ;; be a valid way to produce one that corresponds to the logical definition
  ;; and satisfies the FALTABLE invariants.
  (cond ((atom alist)
         ans)
        ((atom (car alist))
         (hl-fast-alist-fork-aux-really-slow (cdr alist) ans honsp hs))
        (t
         (let* ((key   (hl-hspace-norm (caar alist) hs))
                (entry (hons-assoc-equal key ans)))
           (unless entry
             (if honsp
                 (progn
                   (setq entry (hl-hspace-hons key (cdar alist) hs))
                   (setq ans   (hl-hspace-hons entry ans hs)))
               (progn
                 (setq entry (cons key (cdar alist)))
                 (setq ans   (cons entry ans)))))
           (hl-fast-alist-fork-aux-really-slow (cdr alist) ans honsp hs)))))

(defun hl-fast-alist-fork-aux-slow (alist ans table honsp hs)
  ;; This is somewhat slower than the -fast version, because we don't assume
  ;; ALIST has normed keys.  This is the function we'll use when shrinking an
  ;; ordinary alist with an existing fast alist or with an atom as the ANS.
  (declare (type hl-hspace hs)
           (type hash-table table))
  (cond ((atom alist)
         ans)
        ((atom (car alist))
         (hl-fast-alist-fork-aux-slow (cdr alist) ans table honsp hs))
        (t
         (let* ((key   (hl-hspace-norm (caar alist) hs))
                (entry (gethash key table)))
           (unless entry
             (if honsp
                 (progn
                  (setq entry (hl-hspace-hons key (cdar alist) hs))
                  (setq ans   (hl-hspace-hons entry ans hs))
                  (setf (gethash key table) entry))
               (progn
                 ;; We recons the entry so the resulting alist has normed keys.
                 (setq entry (cons key (cdar alist)))
                 (setq ans   (cons entry ans))
                 (setf (gethash key table) entry))))
           (hl-fast-alist-fork-aux-slow (cdr alist) ans table honsp hs)))))

(defun hl-fast-alist-fork-aux-fast (alist ans table honsp hs)
  ;; This is faster than the -slow version because we assume ALIST has normed
  ;; keys.  This is the function we use to merge two fast alists.
  (declare (type hl-hspace hs)
           (type hash-table table))
  (cond ((atom alist)
         ans)
        ((atom (car alist))
         (hl-fast-alist-fork-aux-fast (cdr alist) ans table honsp hs))
        (t
         (let* ((key   (caar alist))
                (entry (gethash key table)))
           (unless entry
             (if honsp
                 (progn
                   (setq entry (hl-hspace-hons key (cdar alist) hs))
                   (setq ans   (hl-hspace-hons entry ans hs))
                   (setf (gethash key table) entry))
               (progn
                 (setq entry (car alist))
                 (setq ans   (cons entry ans))
                 (setf (gethash key table) entry))))
           (hl-fast-alist-fork-aux-fast (cdr alist) ans table honsp hs)))))


; If ANS is an atom, we are going to create a new hash table for the result.
; What size should we use?  If ALIST is a fast alist, we can see how large its
; table is and use the same size.  Otherwise, if ALIST is an ordinary alist,
; it's more difficult to estimate how large the table ought to be; we guess
; a hashtable size that is the maximum of 60 and 1/8 the length of ALIST.

(defun hl-hspace-fast-alist-fork (alist ans honsp hs)
  (declare (type hl-hspace hs))
  (if (atom alist)
      ans
    (let* ((faltable    (hl-hspace-faltable hs))

           (alist-table
            ;; We see if ALIST has a backing hash table only so that we can use
            ;; it as a size hint and know whether its keys are honsed.
            (let ((slot (hl-faltable-general-lookup alist faltable)))
              (hl-falslot-val slot)))

           (ans-slot (if (atom ans)
                         (hl-faltable-get-free-slot faltable)
                       (hl-faltable-general-lookup ans faltable)))

           (ans-table
            ;; Get the table if it already exists, or build a new one if the
            ;; ans is an atom.
            (if (atom ans)
                ;; Make a new hash table for ANS, with our size guess.
                (hl-mht :size (cond ((natp ans)
                                     (max 60 ans))
                                    (alist-table
                                     ;; CHANGE -- this used to be based on
                                     ;; hash-table-count
                                     (hash-table-size
                                      (the hash-table alist-table)))
                                    (t
                                     (max 60
                                          (ash (len alist) -3)))))
              ;; Reuse the existing table
              (hl-falslot-val ans-slot))))

      ;; Disassociate the ANS alist if it exists so we can modify its table
      ;; without regards to interrupts.
      (setf (hl-falslot-key ans-slot) nil)

      (unless ans-table
        ;; Bad discipline.  ANS is not an atom or fast alist.
        (hl-slow-alist-warning 'fast-alist-fork)
        (return-from hl-hspace-fast-alist-fork
          (hl-fast-alist-fork-aux-really-slow alist ans honsp hs)))

      ;; Good discipline.  Shove ALIST into ANS-TABLE.
      (let ((new-alist
             ;; If ALIST is fast, then by the FAL-HT invariants we know it is a
             ;; proper cons list and already has normed keys, so we can use the
             ;; fast version.  Else, we can't make these assumptions, and have
             ;; to use the slow one.
             (if alist-table
                 (hl-fast-alist-fork-aux-fast alist ans ans-table honsp hs)
               (hl-fast-alist-fork-aux-slow alist ans ans-table honsp hs))))

        (when honsp
          (setq ans-slot (hl-faltable-general-lookup new-alist faltable))
          (when (hl-falslot-key ans-slot)
            ;; "Inadvertent" hash table stealing.
            (hl-alist-stolen-warning 'fast-alist-fork!)
            ;; This slot already has the right key, and must have the right
            ;; value, too.  We've already disassociated the old alist.  So
            ;; we're done.
            (return-from hl-hspace-fast-alist-fork new-alist)))

        (unless (atom new-alist)
          ;; Tricky subtle thing.  If ALIST was a list of atoms, and ANS is an
          ;; atom, then what we arrive at is still an atom.  We don't want any
          ;; atoms bound in the fal-ht, so don't bind it.
          (setf (hl-falslot-val ans-slot) ans-table)
          (setf (hl-falslot-key ans-slot) new-alist))

        new-alist))))

(defun hl-fast-alist-clean-aux (alist ans table honsp hs)

; At the top level, ans is empty and table is a hash table whose keys are
; exactly the keys of alist, but whose values are all nil (which is not a value
; in table; see the Essay on Fast Alists).  We collect the pairs from alist
; into ans, in reverse order, skipping those with a key that is an earlier key
; in alist.  As we add a new pair to ans, we correspondingly update its key in
; table, so that the returned value corresponds to the final table.

  (declare (type hl-hspace hs)
           (type hash-table table))
  (cond
   ((atom alist) ans)
   ((or (atom (car alist))
        (gethash (caar alist) table))
    (hl-fast-alist-clean-aux (cdr alist) ans table honsp hs))
   (t (let* ((key (caar alist))
             (entry (if honsp
                        (hl-hspace-hons key (cdar alist) hs)
                      (car alist)))
             (ans (if honsp
                      (hl-hspace-hons entry ans hs)
                    (cons entry ans))))
        (setf (gethash key table) entry)
        (hl-fast-alist-clean-aux (cdr alist) ans table honsp hs)))))

(defun hl-hspace-fast-alist-clean (alist honsp hs)
  (declare (type hl-hspace hs))
  (cond
   ((atom alist) alist)
   (t
    (let* ((ans (cdr (last alist))) ; preserve final cdr
           (faltable (hl-hspace-faltable hs))
           (slot (hl-faltable-general-lookup alist faltable))
           (table (hl-falslot-val slot)))
      (cond
       ((null table)
        (return-from hl-hspace-fast-alist-clean
                     (hl-hspace-fast-alist-fork alist ans honsp hs)))
       (t
        (setf (hl-falslot-key slot) nil) ; invalidate entry for alist

; We eliminate each value from table, which is useful in
; hl-fast-alist-clean-aux for identifying when a pair in alist is shadowed
; (because its key occurs earlier in alist).  In an experiment with the seven
; supported Lisps, only CLISP reduced the size of the hash-table when using
; clrhash.  Otherwise, clrhash is preferred, at least in CCL where maphash
; appears to do some consing while clrhash does not.

        #-clisp
        (clrhash table)
        #+clisp
        (maphash (lambda (key val)
                   (declare (ignore val))
                   (setf (gethash key table) nil))
                 table)
        (let ((new-alist

; A side effect of the following call is to restore the values in table, so
; that it corresponds to new-alist (equivalently, to alist).

               (hl-fast-alist-clean-aux alist ans table honsp hs)))
          (setf (hl-falslot-key slot) new-alist))))))))

(defun hl-hspace-fast-alist-len (alist hs)
  (declare (type hl-hspace hs))
  (if (atom alist)
      0
    (let* ((faltable (hl-hspace-faltable hs))
           (slot     (hl-faltable-general-lookup alist faltable))
           (val      (hl-falslot-val slot)))
      ;; In the case of good discipline, the slot's key/value are set properly,
      ;; otherwise they are both nil.
      (if val
          (hash-table-count val)
        (progn
          (hl-slow-alist-warning 'fast-alist-len)
          (let* ((fast-alist (hl-hspace-fast-alist-fork alist nil nil hs))
                 (result     (hl-hspace-fast-alist-len fast-alist hs)))
            (hl-hspace-fast-alist-free fast-alist hs)
            result))))))

(defun hl-check-alist-for-serialize-restore (alist hs)

; Causes an error unless every key of ALIST is normed.

  (declare (type hl-hspace hs))
  (cond ((atom alist)
         nil)
        ((atom (car alist))
         (hl-check-alist-for-serialize-restore (cdr alist) hs))
        ((not (hl-hspace-normedp (caar alist) hs))
         (error "Can't restore an alist from the serialized file since it has ~
                 a key that was not re-honsed.~%  ~
                  - Problematic key: ~S~%  ~
                  - Tail of alist: ~S~%"
                (caar alist)
                alist))
        (t
         (hl-check-alist-for-serialize-restore (cdr alist) hs))))

(defun hl-hspace-restore-fal-for-serialize (alist count hs)

; (HL-HSPACE-RESTORE-FAL-FOR-SERIALIZE ALIST COUNT HS) destructively modifies HS.
;   ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;   ** callers should not have ADDR-HT or SBITS let-bound!
;
; ALIST should have just been read from a serialized object, and was marked as
; a fast alist in a previous ACL2 session.  COUNT was its count in the previous
; session, which we will use as its initial size.
;
; If ALIST has any non-honsed keys it is an error, and we check for this case.
; If ALIST already has a hash table, it is a discipline failure.  This could
; perhaps happen due to hons-acons! like stealing, when ALIST is itself a hons.

  (declare (type hl-hspace hs))
  (let* ((faltable  (hl-hspace-faltable hs))
         (slot      (hl-faltable-general-lookup alist faltable))
         (new-ht    (hl-mht :size (max 60 count))))
    (hl-check-alist-for-serialize-restore alist hs)
    (hl-make-fast-alist-put-pairs alist new-ht)
    (when (hl-falslot-val slot)
      ;; BOZO how much of an error is this?  Do we want to warn about it?
      (hl-alist-stolen-warning 'hl-hspace-restore-fal-for-serialize))
    (setf (hl-falslot-val slot) new-ht)
    (setf (hl-falslot-key slot) alist)))

(defun hl-restore-fal-for-serialize (alist count)
  ;; Bootstrapping hack for serialize
  ;; Assumes *default-hs* is already initialized
  (declare (special *default-hs*))
  (hl-hspace-restore-fal-for-serialize alist count *default-hs*))


; CHANGE -- increased size of number-subtrees-ht to start at 10,000.  BOZO
; think about making this higher, or using a more aggressive rehashing size?

(defun hl-hspace-number-subtrees-aux (x seen)
  (declare (type hash-table seen))
  (cond ((atom x)
         nil)
        ((gethash x seen)
         nil)
        (t
         (progn
           (setf (gethash x seen) t)
           (hl-hspace-number-subtrees-aux (car x) seen)
           (hl-hspace-number-subtrees-aux (cdr x) seen)))))

(defun hl-hspace-number-subtrees (x hs)
;   ** may install a new ADDR-HT, SBITS (hons-wash via hl-addr-limit-action)
;   ** callers should not have ADDR-HT or SBITS let-bound!
  (declare (type hl-hspace hs))
  (let ((x    (hl-hspace-norm x hs))
        (seen (hl-mht :test 'eq :size 10000)))
    (hl-hspace-number-subtrees-aux x seen)
    (hash-table-count seen)))

(defun hl-faltable-clear-cache (faltable)

  ;; Destructively modifies HS, if faltable is the faltable of HS.
  ;; Clears the fast alist cache slots, moving any items into the main hash
  ;; table.  This operation should always be safe to use: we are just moving
  ;; things out of the cache and putting them into the table.

  ;; A reason to do this is that we want gc to be able to collect entries whose
  ;; alists are garbage.  Recall that hl-initialize-faltable-table calls hl-mht
  ;; with keyword argument :weak :key, so this works fine for the (weak) hash
  ;; table field of faltable, but the cache slots don't allow for such
  ;; collection.  This function evicts the cache in order to solve that
  ;; problem.

  (declare (type hl-faltable faltable))
  (hl-faltable-eject (hl-faltable-slot1 faltable) faltable)
  (hl-faltable-eject (hl-faltable-slot2 faltable) faltable)
  (setf (hl-faltable-eject1 faltable) nil))

; ----------------------------------------------------------------------
;
;                       CLEARING THE HONS SPACE
;
; ----------------------------------------------------------------------

; This is a barbaric garbage collection mechanism that can be used in Classic
; or Static honsing.
;
; The idea is to throw away all of the honses in the Hons Space, except that we
; then want to restore any "persistent" honses and fast alist keys (so that
; fast alists don't become slow).
;
; It is generally better to use HONS-WASH instead, but that only works in
; Static Honsing.

(defun hl-system-gc ()

; At one time, we thought that ccl::gc only schedules a GC to happen, and we
; worked here to ensure that the GC has actually completed.  However, Gary
; Byers has explained (4/28/15) that all other threads are suspended until
; after the thread performing the GC completes the GC.  But based on an email
; from Bob Boyer sent 2/5/2017, and based on behavior described in
; a comment in hl-hspace-hons-wash, we no longer believe that garbage
; collection is complete when gc$ returns.

  (gc$))

#-static-hons
(defun hl-hspace-classic-restore (x nil-ht cdr-ht cdr-ht-eql seen-ht)

; Returns X and destructively updates the other arguments.
;
; Classic honsing only.  This function is used to restore any persistent honses
; after clearing them.
;
; X is an ACL2 Object that we need to recursively reinstall.  We assume that X
; was previously normed; thus, all of the strings in X are still normed because
; we never clear the STR-HT.
;
; SEEN-HT is an EQ hash table that says which conses we have already
; reinstalled.
;
; The other arguments are the correspondingly named fields in the hons space,
; which we assume are detached from any hons space.  Because of this, we do
; not need to worry about interrupts and can freely update the fields in an
; order that violates the usual hons space invariants.

  (declare (type hash-table nil-ht)
           (type hash-table cdr-ht)
           (type hash-table cdr-ht-eql)
           (type hash-table seen-ht))

  (cond ((atom x)
         ;; Nothing to do because we assume all atoms have already been
         ;; installed.
         x)

        ((gethash x seen-ht)
         ;; Nothing to do because we have already reinstalled X.
         x)

        (t
         (let* ((a (hl-hspace-classic-restore (car x) nil-ht cdr-ht
                                              cdr-ht-eql seen-ht))
                (b (hl-hspace-classic-restore (cdr x) nil-ht cdr-ht
                                              cdr-ht-eql seen-ht)))
           (setf (gethash x seen-ht) t) ;; Mark X as seen.
           (if (eq b nil)
               (setf (gethash a nil-ht) x)
             (let* ((main-table (if (or (consp b)
                                        (symbolp b)
                                        (typep b 'array)) ;; (stringp b)
                                    cdr-ht
                                  cdr-ht-eql))
                    (flex-alist     (gethash b main-table))
                    (was-alistp     (listp flex-alist))
                    (new-flex-alist (hl-flex-acons x flex-alist)))
               ;; If was-alistp, then the flex-acons was applicative and we
               ;; have to install the new flex alist.  Otherwise, it's already
               ;; installed.
               (when was-alistp
                 (setf (gethash b main-table) new-flex-alist))
               x))))))

#-static-hons
(defun hl-hspace-hons-clear (gc hs)
  (declare (type hl-hspace hs))
  (let* ((ctables         (hl-hspace-ctables hs))
         (nil-ht          (hl-ctables-nil-ht ctables))
         (cdr-ht          (hl-ctables-cdr-ht ctables))
         (cdr-ht-eql      (hl-ctables-cdr-ht-eql ctables))
         (faltable        (hl-hspace-faltable hs))
         (persist-ht      (hl-hspace-persist-ht hs))
         (norm-cache      (hl-hspace-norm-cache hs))
         (temp-nil-ht     (hl-mht :test #'eql))
         (temp-cdr-ht     (hl-mht :test #'eq))
         (temp-cdr-ht-eql (hl-mht :test #'eql))
         (temp-ctables    (make-hl-ctables :nil-ht temp-nil-ht
                                           :cdr-ht temp-cdr-ht
                                           :cdr-ht-eql temp-cdr-ht-eql))
         (temp-faltable   (hl-faltable-init))
         (temp-persist-ht (hl-mht :test #'eq))
         (seen-ht         (hl-mht :test #'eq
                                  :size ; arbitrary; probably not important
                                  10000))
         (note-stream (get-output-stream-from-channel *standard-co*)))

    ;; Very subtle.  We're about to violate invariants, so we need to clear out
    ;; the hons space while we work.  Because we aggregated the ctables into a
    ;; single field, we can 'uninstall' the NIL-HT, CDR-HT, and CDR-HT-EQL all
    ;; together with a single setf.  This gives us Ctrl+C safety and means all
    ;; our invariants are preserved.

    ;; Order here is important.  We cannot clear ctables before norm-memo-ht,
    ;; because then we'd have stale allegedly-normed conses in the memo table.
    ;; Similarly we need to clear the fal-ht and persist-ht before the ctables,
    ;; or an interrupt might leave us with stale allegedly normed conses in
    ;; those tables.

    (hl-faltable-clear-cache faltable)
    (hl-cache-clear norm-cache)
    (setf (hl-hspace-faltable hs) temp-faltable)
    (setf (hl-hspace-persist-ht hs) temp-persist-ht)
    (setf (hl-hspace-ctables hs) temp-ctables)

    (format note-stream
            "; Hons-Note: clearing normed objects.~%")

    (clrhash nil-ht)
    (clrhash cdr-ht)
    (clrhash cdr-ht-eql)

    (when gc
      (hl-system-gc))

    (format note-stream
            "; Hons-Note: re-norming persistently normed objects.~%")

    (maphash (lambda (key val)
               (declare (ignore val))
               (hl-hspace-classic-restore key nil-ht cdr-ht cdr-ht-eql seen-ht))
             persist-ht)

    (format note-stream
            "; Hons-Note: re-norming fast alist keys.~%")

    ;; BOZO we probably want to loop over the alist, rather than the associated
    ;; hash table, to avoid the maphash overhead.
    (hl-faltable-maphash
     (lambda (alist associated-hash-table)
       (declare (ignore alist))
       (maphash (lambda (key val)
                  (declare (ignore val))
                  (hl-hspace-classic-restore key nil-ht cdr-ht
                                             cdr-ht-eql seen-ht))
                associated-hash-table))
     faltable)

    (format note-stream
            "; Hons-Note: finished re-norming ~a conses.~%"
            (hash-table-count seen-ht))

    ;; Again order is critical.  Ctables must be installed before fal-ht or
    ;; persist-ht, since parts of fal-ht and persist-ht are expected to be
    ;; normed.
    (setf (hl-hspace-ctables hs) ctables)
    (setf (hl-hspace-faltable hs) faltable)
    (setf (hl-hspace-persist-ht hs) persist-ht))

  nil)

#+static-hons
(defun hl-hspace-static-restore (x addr-ht sbits str-ht other-ht)

; Returns X and destructively modifies ADDR-HT and SBITS.
;
; Static honsing only.  This function is used to restore any persistent honses
; after clearing them.
;
; X is an ACL2 Object that we need to recursively reinstall.  We assume that X
; was previously normed; thus, all of the strings in X are still normed, and
; moreover hl-addr-of etc. are still in good shape, because we never clear the
; STR-HT or (for static honsing) the OTHER-HT.
;
; The other fields are the corresponding fields from a Hons Space, but we
; assume they are detached from any Hons Space and do not need to be updated
; in a manner that maintains their invariants in the face of interrupts.
;
; Note that we don't bother to do anything about the ADDR-LIMIT in this
; function; we basically assume the ADDR-HT is big enough that it isn't going
; to need resizing, and that the caller will fix up the (heuristic) ADDR-LIMIT
; after doing all of the necessary restoration.

  (declare (type hash-table addr-ht)
           (type (simple-array bit (*)) sbits))
  (if (atom x)
      ;; Nothing to do because we assume all atoms have already been installed.
      x
    (let ((index (hl-staticp x)))
      (if (= (aref sbits index) 1)
          ;; Nothing to do; we've already reinstalled X.
          x
        (let* ((a (hl-hspace-static-restore (car x) addr-ht sbits
                                            str-ht other-ht))
               (b (hl-hspace-static-restore (cdr x) addr-ht sbits
                                            str-ht other-ht))
               (addr-a (hl-addr-of a str-ht other-ht))
               (addr-b (hl-addr-of b str-ht other-ht))
               (key    (hl-addr-combine* addr-a addr-b)))
; See comment above about not being concerned with interrupts.
          (setf (aref sbits index) 1)
          (setf (gethash key addr-ht) x)
          x)))))

#+static-hons
(defun hl-hspace-hons-clear (gc hs)
  (declare (type hl-hspace hs))

  #+static-hons
  (clear-memoize-tables) ; See comment about this in hl-hspace-hons-wash.

  (let* ((addr-ht         (hl-hspace-addr-ht hs))
         (sbits           (hl-hspace-sbits hs))
         (sbits-len       (length sbits))
         (faltable        (hl-hspace-faltable hs))
         (persist-ht      (hl-hspace-persist-ht hs))
         (str-ht          (hl-hspace-str-ht hs))
         (other-ht        (hl-hspace-other-ht hs))
         (norm-cache      (hl-hspace-norm-cache hs))
         (temp-faltable   (hl-faltable-init))
         (temp-persist-ht (hl-mht :test #'eq))
         (temp-addr-ht    (hl-mht :test #'eql))
         (temp-sbits      (make-array 1 :element-type 'bit :initial-element 0))
         (note-stream     (get-output-stream-from-channel *standard-co*)))

    ;; Very subtle.  We're about to violate invariants, so we need to clear out
    ;; the hons space while we work.

    ;; See also the classic version; order matters, you can't clear out addr-ht
    ;; and sbits before the other tables.

    (hl-faltable-clear-cache faltable)
    (hl-cache-clear norm-cache)
    (setf (hl-hspace-faltable hs) temp-faltable)
    (setf (hl-hspace-persist-ht hs) temp-persist-ht)
    (without-interrupts
     (setf (hl-hspace-addr-ht hs) temp-addr-ht)
     (setf (hl-hspace-sbits hs) temp-sbits))

    (format note-stream "; Hons-Note: clearing normed objects.~%")

    (clrhash addr-ht)
    (loop for i fixnum below sbits-len do
          (setf (aref sbits i) 0))

    (when gc
      (hl-system-gc))

    (time$ (maphash (lambda (key val)
                      (declare (ignore val))
                      (hl-hspace-static-restore key addr-ht sbits str-ht
                                                other-ht))
                    persist-ht)
           :msg "; Hons-Note: re-norm persistents: ~st seconds, ~sa bytes.~%")

    ;; BOZO we probably want to loop over the alist, rather than the associated
    ;; hash table, to avoid the maphash overhead
    (time$ (hl-faltable-maphash
            (lambda (alist associated-hash-table)
              (declare (ignore alist))
              (maphash (lambda (key val)
                         (declare (ignore val))
                         (hl-hspace-static-restore key addr-ht sbits
                                                   str-ht other-ht))
                       associated-hash-table))
            faltable)
           :msg "; Hons-Note: re-norm fal keys: ~st seconds, ~sa bytes.~%")

    (format note-stream "; Hons-Note: finished re-norming ~:D conses.~%"
            (hash-table-count addr-ht))

    ;; Order matters, reinstall addr-ht and sbits before fal-ht and persist-ht!
    (without-interrupts
     (setf (hl-hspace-addr-ht hs) addr-ht)
     (setf (hl-hspace-sbits hs) sbits))
    (setf (hl-hspace-faltable hs) faltable)
    (setf (hl-hspace-persist-ht hs) persist-ht)

    ;; If an interrupt stops us before here, that's fine; there's no soundness
    ;; burden with the ADDR-LIMIT.
    (hl-make-addr-limit-current hs))

  nil)

; ----------------------------------------------------------------------
;
;                WASHING A HONS SPACE (Static Honsing Only)
;
; ----------------------------------------------------------------------


; BOZO thread unsafe.  It is probably not okay to use this function in a
; multi-threaded environment.  In particular, another thread could create a
; static cons while we were restoring conses, and we'd think it had survived
; the garbage collection.  So, to make this thread safe we would need to add a
; locking mechanism to prevent access to HONS during the restore.  Actually we
; would only need something like (with-lock (gc) (fix-sbits)).  We haven't
; added this locking yet since it would slow down honsing.  But this might be a
; good argument for using a truly shared hons space.

#+static-hons
(defun hl-fix-sbits-after-gc (sbits)

; (HL-FIX-SBITS-AFTER-GC SBITS) destructively modifies SBITS and counts up how
; many normed conses survived the garbage collection.  Each normed cons that
; did not survive has its entry zeroed out.  We return the number of 1 bits in
; the updated SBITS, i.e., the number of normed conses that survived.

; Note that SBITS is _not_ the sbits of a hons space.  Therefore, this function
; need not take responsibility for maintaining a correspondence between SBITS
; and the sbits field of a hons space.

  (declare (type (simple-array bit (*)) sbits))
  (let ((num-survivors 0)
        (max-index     (length sbits)))
    (declare (fixnum max-index)
             (fixnum num-survivors))
    (loop for i fixnum below max-index do
          (when (= (aref sbits i) 1)
            (let ((object (hl-static-inverse-cons i)))
              (if object
                  (incf num-survivors)
                (setf (aref sbits i) 0)))))
    num-survivors))

#+static-hons
(defun hl-rebuild-addr-ht (sbits addr-ht str-ht other-ht)

; (HL-REBUILD-ADDR-HT SBITS ADDR-HT STR-HT OTHER-HT) destructively modifies
; ADDR-HT.
;
; This is a subtle function which is really the key to washing.  We expect that
; SBITS has already been fixed up so that only survivors are marked, but we
; gracefully handle rare cases when some erstwhile survivors died after SBITS
; was already fixed up.
;
; We assume that ADDR-HT is empty to begin with.  We walk over the SBITS and
; install each survivor into its proper place in the ADDR-HT.
;
; The STR-HT and OTHER-HT are only needed for address computations.

  (declare (type (simple-array bit (*)) sbits)
           (type hash-table addr-ht))
  (let ((max-index (length sbits))
        (num-dead-survivors 0))
    (declare (fixnum max-index)
             (fixnum num-dead-survivors))
    (loop for i fixnum below max-index do
          (when (= (aref sbits i) 1)
            ;; This object was previously normed.
            (let ((object (hl-static-inverse-cons i)))
              (cond ((not object)
                     ;; SBITS contained an inconsistent entry, meaning that
                     ;; some static cons was freed after SBITS was fixed up.
                     ;; We amend SBITS on the fly to account for this.
                     (setf (aref sbits i) 0)
                     (incf num-dead-survivors))
                    (t
                     (let* ((a      (car object))
                            (b      (cdr object))
                            ;; It might be that A or B are not actually
                            ;; normed.  So why is it okay to call hl-addr-of?
                            ;; It turns out to be okay.  In the atom case,
                            ;; nothing has changed.  In the cons case, the
                            ;; address calculation only depends on the static
                            ;; index of a and b, which hasn't changed.
                            (addr-a (hl-addr-of a str-ht other-ht))
                            (addr-b (hl-addr-of b str-ht other-ht))
                            (key    (hl-addr-combine* addr-a addr-b)))
                       (setf (gethash key addr-ht) object)))))))
    (when (< 0 num-dead-survivors)
      (let ((note-stream (get-output-stream-from-channel *standard-co*)))
        (format
         note-stream
         "; Hons-Note: ~:D conses unexpectedly disappeared before we could~%~
          ;   restore them, probably because additional garbage collection~%~
          ;   passes occurred after washing.  This is safe, but means that~%~
          ;   we may have allocated more space than necessary for ADDR-HT.~%"
         num-dead-survivors)
        (force-output note-stream)))))

#+static-hons
(defparameter *hl-addr-ht-resize-cutoff*

  ;; After we've GC'd the honses in hons-wash, we will look at how many honses
  ;; survived.  If there are fewer than OLD-SIZE * THRESHOLD honses surviving,
  ;; we'll stay with the old size.  Otherwise, we'll allocate a new hash table
  ;; with room for more entries.  BOZO: This parameter could probably use some
  ;; tuning.

  ;; Explanation:

  ;; We're trying to strike a balance here between a couple of competing
  ;; desires.  Here's a scenario.  We allocate room for 100 million honses and
  ;; then we start up a long-running computation that's going to create 500
  ;; million honses before it's done (but some of these honses are going to be
  ;; ephemeral).

  ;; We get to 100 million honses in and we are out of room, so we have to
  ;; wash.  We start by doing a fancy garbage collection to get rid of whatever
  ;; honses are no longer reachable.  Now we need to decide whether or not we
  ;; should grow the ADDR-HT.  Some cases are easy:

  ;;   - If only 10 million honses are still reachable, then we're doing great:
  ;;     we freed up plenty of space and so we probably won't have to wash
  ;;     again for quite some time.  Don't grow the addr-ht, because it already
  ;;     has plenty of room for continued computation.

  ;;   - If 99 million honses are still reachable, then very few of the honses
  ;;     were ephemeral and it's very likely that in order to keep going we're
  ;;     going to need more space.  We definitely want to grow.  If we don't,
  ;;     we'll just be back here, washing again, after a very short time, and
  ;;     we'll get into a kind of thrashing loop.

  ;; The middle ground is where it's tricky.  At what point is it worth resizing?
  ;; We're picking 0.75 for now.

  0.75)

(defun hl-hspace-hons-wash (hs)

; (HL-HSPACE-HONS-WASH HS) --> NIL and destructively modifies HS
;
; We try to GC normed honses but we do not try to GC normed atoms that might be
; unreachable except for their entries in the STR-HT and OTHER-HT.  We have
; considered how we might extend this function to also collect these atoms, but
; have concluded it probably isn't worth doing.  Basically, we would need to
; separately record the indexes of the static conses in these tables, which is
; fine but would require us to allocate some memory.
;
;    (BOZO it might be possible to make STR-HT and OTHER-HT weak, but I haven't
;     really thought it all the way through.)
;
; IMPORTANT OBLIGATIONS OF THE CALLER.
;
; For this to work correctly in practice, it is critical that the ADDR-HT is
; not LET-bound anywhere in the call stack above this function.  We want
; setting (hl-hspace-addr-ht hs) to NIL to be sufficient to make the ADDR-HT
; unreachable, so that it can be GC'd.
;
; This function can be called by any ordinary hons-creating operation such as
; HL-HSPACE-HONS, HL-HSPACE-HONS-NORM, etc.  This raises some subtle issues,
; because you can imagine "ordinary" implementation level code that looks like
; this:
;
;    (let ((addr-ht (hl-hspace-addr-ht hs))
;          (fal-ht  (hl-hspace-fal-ht hs))
;          (...     (... (hl-hspace-hons ...)))
;          (...     (foo addr-ht fal-ht)))
;       ...)
;
; It would be a very bad error to write something like this: one can no longer
; assume that ADDR-HT is the same after a hons-creating operation.  (This has
; also always been true of SBITS: that is, calling any hons-creating operation
; might alter SBITS).
;
; What about the other Hons Space fields?  Except for the ADDR-HT and SBITS,
; the other fields like the FAL-HT, PERSIST-HT, NORM-CACHE, etc. are all
; restored at the end of a wash, so there's no problem with let-binding them
; and assuming they are the same.  It is only the ADDR-HT and SBITS that we
; must be cautious with.

  (declare (type hl-hspace hs))

  #-static-hons
  (declare (ignore hs))
  #-static-hons
  (format t "; Hons-Note: washing is not available for classic honsing.~%")

; For static honsing, it is also necessary to clear the memoize tables, because
; indices of static conses might be stale.  See the soundness bug example in
; :xdoc topic note-7-0, in community book books/system/doc/acl2-doc.lisp, and
; see the comment about hons-wash in pons-addr-of-argument.  We clear the
; memoize tables before doing anything else, in case a control-c leaves things
; only partly done.

  #+static-hons
  (clear-memoize-tables)

  #+static-hons
  (let* (;; Note: do not bind ADDR-HT here, we want it to get GC'd.
         (addr-ht-size             (hash-table-size (hl-hspace-addr-ht hs)))
         (addr-ht-count            (hash-table-count (hl-hspace-addr-ht hs)))
         (addr-ht-rehash-size      (hash-table-rehash-size
                                    (hl-hspace-addr-ht hs)))
         (addr-ht-rehash-threshold (hash-table-rehash-threshold
                                    (hl-hspace-addr-ht hs)))

         (str-ht        (hl-hspace-str-ht hs))
         (sbits         (hl-hspace-sbits hs))
         (other-ht      (hl-hspace-other-ht hs))
         (faltable      (hl-hspace-faltable hs))
         (persist-ht    (hl-hspace-persist-ht hs))
         (norm-cache    (hl-hspace-norm-cache hs))

         (temp-faltable   (hl-faltable-init))
         (temp-addr-ht    (hl-mht :test #'eql))
         (temp-sbits      (make-array 1 :element-type 'bit :initial-element 0))
         (temp-persist-ht (hl-mht :test #'eq))
         (note-stream     (get-output-stream-from-channel *standard-co*)))

    (format note-stream "; Hons-Note: washing ADDR-HT, ~:D used of ~:D slots.~%"
            addr-ht-count addr-ht-size)
    (force-output note-stream)

    (hl-faltable-clear-cache faltable)

    ;; Clear the (norming) memo table since it might prevent conses from being
    ;; garbage collected and it's unsound to leave it as the sbits/addr-ht are
    ;; cleared.
    (hl-cache-clear norm-cache)

    ;; We need to remove SBITS, FAL-HT, and ADDR-HT from HS before continuing,
    ;; so that if a user interrupts they merely end up with a mostly empty hons
    ;; space instead of an invalid one.  Note that nothing we're about to do
    ;; invalidates the STR-HT or OTHER-HT, so we leave them alone.
    (setf (hl-hspace-faltable hs) temp-faltable)
    (setf (hl-hspace-persist-ht hs) temp-persist-ht)
    (without-interrupts ;; These two must be done together or not at all.
     (setf (hl-hspace-addr-ht hs) temp-addr-ht)
     (setf (hl-hspace-sbits hs) temp-sbits))

    ;; At this point, we can do anything we want with FAL-HT, ADDR-HT, and
    ;; SBITS, because they are no longer part of a Hons Space.
    ;;
    ;; Historically, at this point we did: (CLRHASH ADDR-HT) so that conses
    ;; within it could be garbage collected, explicitly trigger a GC, then
    ;; "magically" restore the surviving conses using the static-inverse-cons
    ;; trick (see HL-REBUILD-ADDR-HT).
    ;;
    ;; But when we added the ADDR-LIMIT stuff, we realized that this would be
    ;; the perfect place to grow the ADDR-HT ourselves instead of allowing the
    ;; Lisp to do it.  Here, we can exploit the magic of static-inverse-cons to
    ;; avoid having to have both the old and new ADDR-HT existing at the same
    ;; time.  So, now we don't CLRHASH the ADDR-HT; we garbage collect it and
    ;; build a new one!  We've already overridden the pointer to ADDR-HT inside
    ;; the hons space.  Unless someone else has it bound (which they
    ;; shouldn't), it can now be GC'd.

    (hl-system-gc)

    ;; Now we fix up the SBITS array by zeroing out any conses that got GC'd,
    ;; and in the process we count how many survivors there are.  This will let
    ;; us make a good decision about resizing the ADDR-HT.  If it would still
    ;; be more than 75% full (or, really, whatever the
    ;; *hl-addr-ht-resize-cutoff* says), we'll make the new table bigger.
    (let* ((num-survivors (hl-fix-sbits-after-gc sbits))
           (pct-full      (/ num-survivors addr-ht-size))
           (addr-ht       nil))

      (when (> pct-full *hl-addr-ht-resize-cutoff*)
        (setq addr-ht-size (floor (* addr-ht-size addr-ht-rehash-size))))

      (format note-stream
              "; Hons-Note: Making new ADDR-HT with size ~:D~%"
              addr-ht-size)
      (force-output note-stream)

      ;; This can take several seconds...
      (setq addr-ht (hl-mht :test #'eql
                            :size addr-ht-size
                            :rehash-size      addr-ht-rehash-size
                            :rehash-threshold addr-ht-rehash-threshold))

      (format note-stream "; Hons-Note: Restoring ~:D conses~%" num-survivors)
      (force-output note-stream)

      ;; This can take hundreds of seconds...
      (hl-rebuild-addr-ht sbits addr-ht str-ht other-ht)
      (format note-stream "; Hons-Note: Done restoring~%")
      (force-output note-stream)

      ;; All objects restored.  The hons space should now be in a fine state
      ;; once again.  Restore it.
      (without-interrupts
       (setf (hl-hspace-addr-ht hs) addr-ht)
       (setf (hl-hspace-sbits hs) sbits))
      (setf (hl-hspace-persist-ht hs) persist-ht)
      (setf (hl-hspace-faltable hs) faltable)
      (hl-make-addr-limit-current hs)))
  nil)

(defun hl-maybe-resize-ht (size src)

; (HL-MAYBE-RESIZE-HT SIZE SRC) --> HASH TABLE
;
; SRC is a hash table that we would perhaps like to resize, and SIZE is our new
; target size.  If SIZE is not sufficiently different from the current size of
; SRC, or if it seems too small for SRC, we just return SRC unchanged.
; Otherwise, we produce a new hash table that is a copy of SRC, but with the
; newly desired SIZE.

  (declare (type hash-table src))
  (let* ((src-size            (hash-table-size src))
         (src-count           (hash-table-count src))

; We bind min-reasonable-size to at least 100 simply because that seems like a
; reasonable minimum size for a hash table.  But we also insist that a new hash
; table should have size at least 1.2 times the existing hash-table-count, so
; that there's a little room to grow.

         (min-reasonable-size (max 100 (* src-count 1.2)))
         (target-size         (max min-reasonable-size size)))
    (if (and (< (* src-size 0.8) target-size)
             (< target-size (* src-size 1.2)))
        ;; You're already pretty close to the target size.  Don't
        ;; bother resizing.
        src
      ;; Okay, size is different enough to warrant resizing.
      (let ((new-ht (hl-mht :test (hash-table-test src)
                            :size size)))
        (maphash (lambda (key val)
                   (setf (gethash key new-ht) val))
                 src)
        new-ht))))

(defun hl-hspace-resize (str-ht-size nil-ht-size cdr-ht-size cdr-ht-eql-size
                         addr-ht-size other-ht-size sbits-size
                         fal-ht-size persist-ht-size
                         hs)
  ;; This is mostly entirely straightforward.

  (declare (type hl-hspace hs)
           #+static-hons
           (ignore nil-ht-size cdr-ht-size cdr-ht-eql-size)
           #-static-hons
           (ignore addr-ht-size other-ht-size sbits-size))

  (when (natp str-ht-size)
    (setf (hl-hspace-str-ht hs)
          (hl-maybe-resize-ht str-ht-size (hl-hspace-str-ht hs))))

  (when (natp fal-ht-size)
    (let* ((faltable (hl-hspace-faltable hs))
           (table    (hl-faltable-table faltable)))
      (setf (hl-faltable-table faltable)
            (hl-maybe-resize-ht fal-ht-size table))))

  (when (natp persist-ht-size)
    (setf (hl-hspace-persist-ht hs)
          (hl-maybe-resize-ht persist-ht-size (hl-hspace-persist-ht hs))))

  #+static-hons
  (progn
    (when (natp addr-ht-size)
      (setf (hl-hspace-addr-ht hs)
            (hl-maybe-resize-ht addr-ht-size (hl-hspace-addr-ht hs))))
    (when (natp other-ht-size)
      (setf (hl-hspace-other-ht hs)
            (hl-maybe-resize-ht other-ht-size (hl-hspace-other-ht hs))))

    (when (natp sbits-size)
      ;; Tricky.  Need to be sure that all 1-valued sbits are preserved.
      ;; We won't try to support shrinking sbits.
      (let* ((sbits    (hl-hspace-sbits hs))
             (new-len  (min (1- array-total-size-limit) sbits-size))
             (curr-len (length sbits)))
        (when (> sbits-size curr-len)
          ;; User wants to grow sbits, so that's okay.
          (let ((new-sbits (make-array new-len
                                       :element-type 'bit
                                       :initial-element 0)))
            (declare (type (simple-array bit (*)) new-sbits))
            (loop for i fixnum below curr-len do
                  (setf (aref new-sbits i) (aref sbits i)))
            (setf (hl-hspace-sbits hs) new-sbits))))))

  #-static-hons
  (let ((ctables (hl-hspace-ctables hs)))
    (when (natp nil-ht-size)
      (setf (hl-ctables-nil-ht ctables)
            (hl-maybe-resize-ht nil-ht-size (hl-ctables-nil-ht ctables))))
    (when (natp cdr-ht-size)
      (setf (hl-ctables-cdr-ht ctables)
            (hl-maybe-resize-ht cdr-ht-size (hl-ctables-cdr-ht ctables))))
    (when (natp cdr-ht-eql-size)
      (setf (hl-ctables-cdr-ht-eql ctables)
            (hl-maybe-resize-ht cdr-ht-eql-size
                                (hl-ctables-cdr-ht-eql ctables)))))

  #+static-hons
  (hl-make-addr-limit-current hs)

  nil)




; ----------------------------------------------------------------------
;
;                         STATISTICS GATHERING
;
; ----------------------------------------------------------------------

(defun hl-get-final-cdr (alist)
  (if (atom alist)
      alist
    (hl-get-final-cdr (cdr alist))))

(defun hl-hspace-fast-alist-summary (hs)
  (declare (type hl-hspace hs))
  (let* ((faltable (hl-hspace-faltable hs))
         (table    (hl-faltable-table faltable))
         (total-count 0)
         (total-sizes 0)
         (total-num 0)
         (report-entries))

    (format t "~%Fast Alists Summary:~%~%")
    (force-output)
    (hl-faltable-maphash
     (lambda (alist associated-ht)
       (let* ((final-cdr (hl-get-final-cdr alist))
              (size      (hash-table-size associated-ht))
              (count     (hash-table-count associated-ht)))
         (incf total-sizes size)
         (incf total-count count)
         (incf total-num)
         (push (list count size final-cdr) report-entries)))
     faltable)
    (format t " - Number of fast alists: ~15:D~%" total-num)
    (format t " - Size of FAL table:     ~15:D~%" (hash-table-size table))
    (format t " - Total of counts:       ~15:D~%" total-count)
    (format t " - Total of sizes:        ~15:D~%" total-sizes)
    (format t "~%")
    (force-output)
    (setq report-entries
          (sort report-entries (lambda (x y)
                                 (or (> (first x) (first y))
                                     (and (= (first x) (first y))
                                          (> (second x) (second y)))))))
    (format t "Summary of individual fast alists:~%~%")
    (format t "      Count           Size         Name~%")
    (format t "  (used slots)     (capacity)~%")
    (format t "--------------------------------------------------~%")
    (loop for entry in report-entries do
          (format t "~10:D ~16:D        ~:D~%"
                  (first entry) (second entry) (third entry)))
    (format t "--------------------------------------------------~%")
    (format t "~%")
    (force-output)))


(defun hl-hspace-hons-summary (hs)
  (declare (type hl-hspace hs))
  (format t "~%Normed Objects Summary~%~%")

  #+static-hons
  (let ((addr-ht  (hl-hspace-addr-ht hs))
        (sbits    (hl-hspace-sbits hs))
        (other-ht (hl-hspace-other-ht hs)))
    (format t " - SBITS array length:    ~15:D~%"
            (length sbits))
    (format t "   New static cons index: ~15:D~%~%"
            (hl-staticp (hl-static-cons nil nil)))
    (format t " - ADDR-HT:      ~15:D count, ~15:D size (~5,2f% full)~%"
            (hash-table-count addr-ht)
            (hash-table-size addr-ht)
            (* (/ (hash-table-count addr-ht)
                  (hash-table-size addr-ht))
               100.0))
    (format t " - OTHER-HT:     ~15:D count, ~15:D size (~5,2f% full)~%"
            (hash-table-count other-ht)
            (hash-table-size other-ht)
            (* (/ (hash-table-count other-ht)
                  (hash-table-size other-ht))
               100.0))
    )

  #-static-hons
  (let* ((ctables    (hl-hspace-ctables hs))
         (nil-ht     (hl-ctables-nil-ht ctables))
         (cdr-ht     (hl-ctables-cdr-ht ctables))
         (cdr-ht-eql (hl-ctables-cdr-ht-eql ctables)))
    (format t " - NIL-HT:       ~15:D count, ~15:D size (~5,2f% full)~%"
            (hash-table-count nil-ht)
            (hash-table-size nil-ht)
            (* (/ (hash-table-count nil-ht)
                  (hash-table-size nil-ht))
               100.0))
    (format t " - CDR-HT:       ~15:D count, ~15:D size (~5,2f% full)~%"
            (hash-table-count cdr-ht)
            (hash-table-size cdr-ht)
            (* (/ (hash-table-count cdr-ht)
                  (hash-table-size cdr-ht))
               100.0))
    (format t " - CDR-HT-EQL:   ~15:D count, ~15:D size (~5,2f% full)~%"
            (hash-table-count cdr-ht-eql)
            (hash-table-size cdr-ht-eql)
            (* (/ (hash-table-count cdr-ht-eql)
                  (hash-table-size cdr-ht-eql))
               100.0))
    )

  (let ((str-ht       (hl-hspace-str-ht hs))
        (persist-ht   (hl-hspace-persist-ht hs))
        (fal-ht       (hl-faltable-table (hl-hspace-faltable hs))))
    (format t " - STR-HT:       ~15:D count, ~15:D size (~5,2f% full)~%"
            (hash-table-count str-ht)
            (hash-table-size str-ht)
            (* (/ (hash-table-count str-ht)
                  (hash-table-size str-ht))
               100.0))
    (format t " - PERSIST-HT:   ~15:D count, ~15:D size (~5,2f% full)~%"
            (hash-table-count persist-ht)
            (hash-table-size persist-ht)
            (* (/ (hash-table-count persist-ht)
                  (hash-table-size persist-ht))
               100.0))
    (format t " - FAL-HT:       ~15:D count, ~15:D size (~5,2f% full)~%~%"
            (hash-table-count fal-ht)
            (hash-table-size fal-ht)
            (* (/ (hash-table-count fal-ht)
                  (hash-table-size fal-ht))
               100.0))
    )

  nil)



; ----------------------------------------------------------------------
;
;                         USER-LEVEL WRAPPERS
;
; ----------------------------------------------------------------------

(defparameter *default-hs*

; We hide the hons space from the ACL2 user by making all ACL2-visible
; functions operate with respect to *default-hs*, the "default hons space."
;
; We allow *default-hs* to be either NIL or a valid hons space.  This is useful
; for ACL2(p) or other (e.g., ttag-based, raw lisp) uses of parallelism.  The
; idea is to allow threads that don't do any honsing to avoid the overhead of
; creating a hons space.  For instance, in ACL2(p), the function
; consume-work-on-work-queue-when-there is responsible for creating all worker
; threads.  This function immediately binds *default-hs* to NIL, which is quite
; cheap.  The first time such a thread needs a hons, a fresh hons space will
; then be automatically created.

   (hl-hspace-init))

(declaim (type (or hl-hspace null) *default-hs*))

(declaim (inline hl-maybe-initialize-default-hs))

(defun hl-maybe-initialize-default-hs ()
  (unless *default-hs*
    (setq *default-hs* (hl-hspace-init))))

(defun hl-maybe-initialize-default-hs-wrapper ()
  ;; Bootstrapping hack for serialize
  (hl-maybe-initialize-default-hs))

(defun hons (x y)
  ;; hl-hspace-hons is inlined via defmacro
  (hl-maybe-initialize-default-hs)
  (hl-hspace-hons x y *default-hs*))

(defun hons-copy (x)
  ;; hl-hspace-norm is inlined
  (hl-maybe-initialize-default-hs)
  (hl-hspace-norm x *default-hs*))

(defun hons-copy-persistent (x)
  ;; no need to inline
  (hl-maybe-initialize-default-hs)
  (hl-hspace-persistent-norm x *default-hs*))

(declaim (inline hons-equal))
(defun hons-equal (x y)
  ;; hl-hspace-hons-equal is not inlined, so we inline the wrapper
  (hl-maybe-initialize-default-hs)
  (hl-hspace-hons-equal x y *default-hs*))

(declaim (inline hons-equal-lite))
(defun hons-equal-lite (x y)
  ;; hl-hspace-hons-equal-lite is not inlined, so we inline the wrapper
  (hl-maybe-initialize-default-hs)
  (hl-hspace-hons-equal-lite x y *default-hs*))

(defun hons-summary ()
  ;; no need to inline
  (hl-maybe-initialize-default-hs)
  (hl-hspace-hons-summary *default-hs*))

(defun hons-clear! (gc)
  ;; no need to inline
  (hl-maybe-initialize-default-hs)
  (hl-hspace-hons-clear gc *default-hs*))

(defun hons-clear (gc)
  ;; no need to inline

; Warning: Keep in sync with hons-wash.

  #+acl2-par
  (when (and (f-get-global 'parallel-execution-enabled *the-live-state*)
             #+ccl
             (not (all-worker-threads-are-dead-or-reset))
             #-ccl

; Currently only CCL, SBCL, and LispWorks support ACL2(p) builds.  We do not
; currently have sufficient confidence in worker-threads for SBCL and LispWorks
; (as per email from David Rager, 4/18/2015) to use the test above, so for
; those Lisps we simply insist on using hons-clear! instead when parallel
; execution is enabled.

             t)
    (return-from hons-clear
                 (with-live-state
                  (progn (warning$ 'hons-clear "Hons-clear"
                                   "Skipping hons-clear call in ACL2(p).  You ~
                                    can avoid this issue by using hons-clear! ~
                                    or by turning off parallel execution; see ~
                                    :DOC hons-clear! and :DOC ~
                                    set-parallel-execution.")
                         nil))))
  (hons-clear! gc))

(defun hons-wash! ()
  (hl-maybe-initialize-default-hs)
  (hl-hspace-hons-wash *default-hs*)
  nil)

(defun hons-wash ()
  ;; no need to inline

; Warning: Keep in sync with hons-clear.

  #+(and acl2-par static-hons)

; Hons-wash is already a no-op when #-static-hons, so there is no reason to do
; the preemptive return just below.  Indeed, such a return would be misleading
; since it may suggest that hons-wash! could have some effect, which is not the
; case when #-static-hons.

  (when (and (f-get-global 'parallel-execution-enabled *the-live-state*)
             #+ccl
             (not (all-worker-threads-are-dead-or-reset))
             #-ccl

; This case is impossible, as only CCL supports both features (acl2-par and
; static-hons): only CCL and GCL support static-hons but GCL does not support
; ACL2(p) builds.  This value of t is acceptable at any rate, though perhaps
; more severe than necessary if some additional Lisp could be supported here.

             t)
    (return-from hons-wash
                 (with-live-state
                  (progn (warning$ 'hons-wash "Hons-wash"
                                   "Skipping hons-wash call in ACL2(p).  You ~
                                    can avoid this issue by using hons-wash! ~
                                    or by turning off parallel execution; see ~
                                    :DOC hons-wash! and :DOC ~
                                    set-parallel-execution.")
                         nil))))
  (hons-wash!))

(defun hons-resize-fn (str-ht nil-ht cdr-ht cdr-ht-eql
                                 addr-ht other-ht sbits
                                 fal-ht persist-ht)
  ;; no need to inline
  (hl-maybe-initialize-default-hs)
  (hl-hspace-resize str-ht nil-ht cdr-ht cdr-ht-eql
                    addr-ht other-ht sbits
                    fal-ht persist-ht
                    *default-hs*))


(declaim (inline hons-acons))
(defun hons-acons (key val fal)
  ;; hl-hspace-hons-acons is not inlined, so we inline the wrapper
  (hl-maybe-initialize-default-hs)
  (hl-hspace-hons-acons key val fal *default-hs*))

(declaim (inline hons-acons!))
(defun hons-acons! (key val fal)
  ;; hl-hspace-hons-acons is not inlined, so we inline the wrapper
  (hl-maybe-initialize-default-hs)
  (hl-hspace-hons-acons! key val fal *default-hs*))

(defun fast-alist-fork (alist ans)
  ;; no need to inline
  (hl-maybe-initialize-default-hs)
  (hl-hspace-fast-alist-fork alist ans nil *default-hs*))

(defun fast-alist-fork! (alist ans)
  ;; no need to inline
  (hl-maybe-initialize-default-hs)
  (hl-hspace-fast-alist-fork alist ans t *default-hs*))

(defun fast-alist-clean (alist)
  ;; no need to inline
  (hl-maybe-initialize-default-hs)
  (hl-hspace-fast-alist-clean alist nil *default-hs*))

(defun fast-alist-clean! (alist)
  ;; no need to inline
  (hl-maybe-initialize-default-hs)
  (hl-hspace-fast-alist-clean alist t *default-hs*))

(declaim (inline hons-get))
(defun hons-get (key fal)
  ;; hl-hspace-hons-get is not inlined, so we inline the wrapper
  (hl-maybe-initialize-default-hs)
  (hl-hspace-hons-get key fal *default-hs*))

(declaim (inline fast-alist-free))
(defun fast-alist-free (fal)
  ;; hl-hspace-fast-alist-free is not inlined, so we inline the wrapper
  (hl-maybe-initialize-default-hs)
  (hl-hspace-fast-alist-free fal *default-hs*))

(declaim (inline fast-alist-len))
(defun fast-alist-len (fal)
  ;; hl-hspace-fast-alist-len is not inlined, so we inline the wrapper
  (hl-maybe-initialize-default-hs)
  (hl-hspace-fast-alist-len fal *default-hs*))

(declaim (inline number-subtrees))
(defun number-subtrees (x)
  ;; hl-hspace-number-subtrees is not inlined, so we inline the wrapper
  (hl-maybe-initialize-default-hs)
  (hl-hspace-number-subtrees x *default-hs*))

(defun fast-alist-summary ()
  ;; no need to inline
  (hl-maybe-initialize-default-hs)
  (hl-hspace-fast-alist-summary *default-hs*))

(defun make-fast-alist (alist)
  ;; no need to inline
  (hl-maybe-initialize-default-hs)
  (hl-hspace-make-fast-alist alist *default-hs*))

(defmacro with-fast-alist-raw (alist form)
  (let ((alist-was-fast-p (gensym))
        (alist-var (if (legal-variablep alist)
                       alist
                     (gensym))))
    `(progn
       (hl-maybe-initialize-default-hs)
       (let* (
              ;; If alist isn't a variable, then depend on it being a
              ;; computation that returns the same (eq) object each time, and
              ;; that object can be turned into an (eq) fast alist, i.e. its
              ;; keys are normed.  If not, then the user may not find their
              ;; alist to be fast during the execution of form, but we'll still
              ;; correctly free it.
              (,alist-var ,alist)
              (,alist-was-fast-p
               (let ((slot (hl-faltable-general-lookup
                            ,alist-var
                            (hl-hspace-faltable *default-hs*))))
                 (if (hl-falslot-key slot)
                     t
                   nil)))
              (,alist-var (if ,alist-was-fast-p
                              ,alist-var
                            (make-fast-alist ,alist-var))))
         (our-multiple-value-prog1
          ,form
          (if ,alist-was-fast-p
              nil
            (fast-alist-free ,alist-var)))))))

(defmacro with-stolen-alist-raw (alist form)
  (let ((alist-was-fast-p (gensym))
        (alist-var (if (legal-variablep alist)
                       alist
                     (gensym))))
    `(progn
       (hl-maybe-initialize-default-hs)
       (let* (
              ;; If alist isn't a variable, then depend on it being a
              ;; computation that returns the same (eq) object each time, and
              ;; that object can be turned into an (eq) fast alist, i.e. its
              ;; keys are normed.  If not, then the user may not find their
              ;; alist to be fast during the execution of form, but we'll still
              ;; correctly free it.
              (,alist-var ,alist)
              (,alist-was-fast-p
               (let ((slot (hl-faltable-general-lookup
                            ,alist-var
                            (hl-hspace-faltable *default-hs*))))
                 (if (hl-falslot-key slot)
                     t
                   nil)))
              (,alist-var (if ,alist-was-fast-p
                              ,alist-var
                            (make-fast-alist ,alist-var))))
         (our-multiple-value-prog1
          ,form
          (if ,alist-was-fast-p
              (make-fast-alist ,alist-var)
            (fast-alist-free ,alist-var)))))))

(defmacro fast-alist-free-on-exit-raw (alist form)
  `(our-multiple-value-prog1
    ,form
    (fast-alist-free ,alist)))


