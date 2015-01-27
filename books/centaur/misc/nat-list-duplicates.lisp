; Duplicate-related functions for lists of natural numbers
; Copyright (C) 2010 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

; nat-list-duplicates.lisp
;  - see :doc nat-list-remove-duplicates, below, for documentation

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "std/lists/remove-duplicates" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "arithmetic/nat-listp" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "tools/mv-nth" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))


(defsection nat-list-remove-duplicates
  :parents (remove-duplicates)
  :short "High-performance duplicate-removal function for @(see nat-listp)s."

  :long "<p>@(call nat-list-remove-duplicates) is logically equal to:</p>

@({
    (revappend (hons-remove-duplicates x) nil)
})

<p>We leave this definition enabled, so typically you will want to just reason
about @(see hons-remove-duplicates) and @(see revappend).</p>

<p>In the execution, we first inspect the list and then heuristically decide
how to carry out the computation.</p>

<p>When the list is very short, we use a naive, quadratic function in the
spirit of @(see remove-duplicates), which avoids the costs of allocating any
seen tables and practically speaking seems to be the fastest way to go.</p>

<p>For longer lists, our usual approach is to implement a seen table as a
bit-array, using a local stobj that is kept hidden from the caller.  This
approach performs very well for most lists that we encounter in practice, and
its memory overhead is relatively low because, at least on CCL, bit arrays
really do get implemented in an efficient way and, aside from some header
information, only require one bit per entry.</p>

<p>Of course, a bit-array is not appropriate when the list contains elements
that are particularly large numbers.  The storage required for the bit array is
just based upon the maximum element in the list.  Here are some examples:</p>

@({
  2^21: 256 KB    2^24: 2 MB    2^27: 16 MB
  2^22: 512 KB    2^25: 4 MB    2^28: 32 MB
  2^23: 1 MB      2^26: 8 MB    2^29: 64 MB
})

<p>In some rare cases, it may actually be worth allocating hundreds of
megabytes of memory to remove duplicates from a list.  But most of the time, if
a list contains numbers in the millions or more, an array-based approach
probably isn't what we want to do, because the list is probably relatively
sparse.  Instead, we should just use a hash table.</p>

<p>We therefore adopt a heuristic for which algorithm to use.  If the maximum
element is under 2^17, then we always use the array since it requires us to
allocate at most 16 KB.  Since 2^17 = 131,072, this is really sufficient to
address a lot of lists that actually arise in practice.</p>

<p>If the maximum is over 2^17, we:</p>

<ul>

<li>again use the naive algorithm unless there are more than a few hundred
elements in the list, because experimentally it's cheaper.</li>

<li>use the array algorithm if there are more than max/256 elements in the
list, which is just pulled out of the air and hasn't really been tested in any
systematic way.  But just as an example, if the maximum element in our list is
2^22 (slightly over 4 million), we'll only allocate the 2 MB array if there are
more than 16,000 elements in the list.  If the maximum element is 2^29 (about
536 million), we'll only allocate the 64 MB array if there are more than two
million elements in the list.</li>

<li>essentially fall back to using @(see hons-remove-duplicates) otherwise.  In
this case, there are too many elements to use the naive algorithm, but not
enough to warrant allocating an array.  So, we want to use the hash table since
it can handle sparse lists well.</li>

</ul>")


(local
 (defsection support

   (defthm positive-when-natp
     (implies (natp x)
              (<= 0 x)))

   (defthm integerp-when-natp
     (implies (natp x)
              (integerp x)))

   (defthm acl2-numberp-when-integerp
     (implies (integerp x)
              (acl2-numberp x)))))

(local (in-theory (enable nat-listp)))


(defsection max-nat

  (defund max-nat-exec (x best)
    (declare (xargs :guard (and (nat-listp x)
                                (natp best))))
    (if (atom x)
        best
      (max-nat-exec (cdr x)
                    (if (> (car x) best)
                        (car x)
                      best))))

  (defund max-nat (x)
    (declare (xargs :guard (nat-listp x)
                    :verify-guards nil))
    (mbe :logic (if (atom x)
                    0
                  (max (car x)
                       (max-nat (cdr x))))
         :exec (max-nat-exec x 0)))

  (defthm natp-of-max-nat
    (implies (force (nat-listp x))
             (natp (max-nat x)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable max-nat))))

  (local (defthm max-nat-exec-removal
           (implies (and (nat-listp x)
                         (natp best))
                    (equal (max-nat-exec x best)
                           (max best (max-nat x))))
           :hints(("Goal"
                   :induct (max-nat-exec x best)
                   :in-theory (enable max-nat-exec max-nat)))))

  (verify-guards max-nat
    :hints(("Goal" :in-theory (enable max-nat)))))

(local (in-theory (enable max-nat)))



(defund max-nat-and-len (x max len)
  (declare (xargs :guard (and (nat-listp x)
                              (natp max)
                              (natp len))))
  (if (atom x)
      (mv max len)
    (max-nat-and-len (cdr x)
                     (if (> (car x) max) (car x) max)
                     (+ 1 len))))

(defthm max-nat-and-len-removal
  (implies (and (force (nat-listp x))
                (force (natp max))
                (force (natp len)))
           (equal (max-nat-and-len x max len)
                  (mv (max max (max-nat x)) (+ len (len x)))))
  :hints(("Goal" :in-theory (enable max-nat-and-len))))




(defund hons-remove-duplicates1-tail (l tab acc)
  (declare (xargs :guard t))
  (cond ((atom l)
         (progn$ (fast-alist-free tab)
                 acc))
        ((hons-get (car l) tab)
         (hons-remove-duplicates1-tail (cdr l) tab acc))
        (t
         (hons-remove-duplicates1-tail (cdr l)
                                       (hons-acons (car l) t tab)
                                       (cons (car l) acc)))))

(defthm hons-remove-duplicates1-tail-removal
  (equal (hons-remove-duplicates1-tail l tab acc)
         (revappend (hons-remove-duplicates1 l tab)
                    acc))
  :hints(("Goal" :in-theory (enable hons-remove-duplicates1-tail
                                    hons-remove-duplicates1))))



(defund nat-remove-dups-very-short-p (x)
  ;; When the list is very short, it's better not to do any allocation at all,
  ;; and just use the naive algorithm.
  (declare (xargs :guard (nat-listp x)))
  (let ((5cdrs  (cdr (cdr (cdr (cdr (cdr x)))))))
    (or (atom 5cdrs)
        (let ((10cdrs (cdr (cdr (cdr (cdr (cdr 5cdrs)))))))
          (or (atom 10cdrs)
              (atom (cdr (cdr (cdr (cdr (cdr 10cdrs)))))))))))

(defund nat-remove-dups-when-very-short (x acc seen)
  (declare (xargs :guard (and (nat-listp x)
                              (nat-listp seen))))
  (cond ((atom x)
         acc)
        ((member (car x) seen)
         (nat-remove-dups-when-very-short (cdr x) acc seen))
        (t
         (nat-remove-dups-when-very-short (cdr x)
                                          (cons (car x) acc)
                                          (cons (car x) seen)))))

(defund nat-remove-dups-when-very-short-solo (x acc)
  (declare (xargs :guard (and (nat-listp x)
                              (nat-listp acc))))
  (cond ((atom x)
         acc)
        ((member (car x) acc)
         (nat-remove-dups-when-very-short-solo (cdr x) acc))
        (t
         (nat-remove-dups-when-very-short-solo (cdr x)
                                               (cons (car x) acc)))))

(local
 (encapsulate
   ()
   (local
    (defthm l1
      (implies (equal acc seen)
               (equal (nat-remove-dups-when-very-short x acc seen)
                      (nat-remove-dups-when-very-short-solo x acc)))
      :hints(("Goal"
              :induct (nat-remove-dups-when-very-short x acc seen)
              :in-theory (enable nat-remove-dups-when-very-short-solo
                                 nat-remove-dups-when-very-short)))))

   (defthm nat-remove-dups-when-very-short-solo-removal
     (equal (nat-remove-dups-when-very-short-solo x nil)
            (nat-remove-dups-when-very-short x nil nil)))))


(local
 (defun dumb-make-table (x)
   (if (atom x)
       nil
     (hons-acons (car x) t (dumb-make-table (cdr x))))))

(local
 (defthm hons-assoc-equal-dumb-make-table
   (equal (hons-assoc-equal a (dumb-make-table x))
          (if (member a x)
              (cons a t)
            nil))
   :hints(("Goal" :in-theory (enable dumb-make-table)))))

(local
 (defthm nat-remove-dups-when-very-short-removal
   (equal (nat-remove-dups-when-very-short x acc seen)
          (revappend (hons-remove-duplicates1 x (dumb-make-table seen))
                     acc))
   :hints(("Goal"
           :induct (nat-remove-dups-when-very-short x acc seen)
           :in-theory (enable nat-remove-dups-when-very-short
                              hons-remove-duplicates1)))))



(defstobj nat-remove-dups-stobj
  (nat-remove-dups-arr :type (array bit (0))
                       :initially 0
                       :resizable t)
  (nat-remove-dups-sparse :type (array integer (0))
                          :initially 0
                          :resizable t)
  :inline t)


(local
 (defsection stobj-nonsense

   (local (defthm natp-of-nat-remove-dups-arrp
            (implies (and (nat-remove-dups-arrp arr)
                          (< (nfix n) (len arr)))
                     (natp (nth n arr)))
            :hints(("Goal" :in-theory (enable nat-remove-dups-arrp)))))

   (defthm natp-of-nat-remove-dups-arri
     (implies (and (force (nat-remove-dups-stobjp st))
                   (force (< (nfix n) (nat-remove-dups-arr-length st))))
              (natp (nat-remove-dups-arri n st)))
     :hints(("Goal" :in-theory (enable nat-remove-dups-arrp))))


   (local (defthm upper-bound-of-nat-remove-dups-arrp
            (implies (and (nat-remove-dups-arrp arr)
                          (< (nfix n) (len arr)))
                     (< (nth n arr) 2))
            :rule-classes ((:rewrite) (:linear))))

   (defthm upper-bound-of-nat-remove-dups-arri
     (implies (and (force (nat-remove-dups-stobjp st))
                   (force (< (nfix n) (nat-remove-dups-arr-length st))))
              (< (nat-remove-dups-arri n st) 2))
     :rule-classes ((:rewrite) (:linear)))

   (defthm update-nat-remove-dups-arri-preserves-len
     (implies (force (< (nfix key) (nat-remove-dups-arr-length st)))
              (equal (nat-remove-dups-arr-length (update-nat-remove-dups-arri key val st))
                     (nat-remove-dups-arr-length st))))

   (defthm nat-remove-dups-arri-of-update-nat-remove-dups-arri-diff
     (implies (and (force (< key1 (nat-remove-dups-arr-length st)))
                   (force (< key2 (nat-remove-dups-arr-length st)))
                   (force (natp key1))
                   (force (natp key2)))
              (equal (nat-remove-dups-arri key1 (update-nat-remove-dups-arri key2 val st))
                     (if (equal key1 key2)
                         val
                       (nat-remove-dups-arri key1 st)))))

   (defthm nat-remove-dups-arr-length-of-resize-nat-remove-dups-arr
     (equal (nat-remove-dups-arr-length (resize-nat-remove-dups-arr len st))
            (nfix len)))

   (defthm nat-remove-dups-arr-length-of-create-nat-remove-dups-stobj
     (equal (nat-remove-dups-arr-length (create-nat-remove-dups-stobj))
            0))

   (defthm nat-remove-dups-arri-of-resize-nat-remove-dups-arr
     (implies (and (force (natp key))
                   (force (natp max))
                   (force (< key max)))
              (equal (nat-remove-dups-arri key (resize-nat-remove-dups-arr max st))
                     (if (< key (nat-remove-dups-arr-length st))
                         (nat-remove-dups-arri key st)
                       0))))))

(local (in-theory (disable nat-remove-dups-arri
                           update-nat-remove-dups-arri
                           nat-remove-dups-arr-length
                           nat-remove-dups-stobjp
                           create-nat-remove-dups-stobj
                           resize-nat-remove-dups-arr)))



(defund nat-remove-dups-with-stobj-aux (x max acc nat-remove-dups-stobj)
  ;; Core function.  Similar to hons-duplicates1 except that we use a stobj
  ;; instead of a fast alist, and we write the function tail recursively.
  "Returns (MV ACC STOBJ)"
  (declare (xargs :guard (and (nat-listp x)
                              (natp max)
                              (<= (max-nat x) max)
                              (< max (nat-remove-dups-arr-length nat-remove-dups-stobj)))
                  :stobjs nat-remove-dups-stobj))
  (cond ((atom x)
         (mv acc nat-remove-dups-stobj))
        ((= 1 (the (unsigned-byte 1)
                   (nat-remove-dups-arri (car x) nat-remove-dups-stobj)))
         ;; Already saw it
         (nat-remove-dups-with-stobj-aux (cdr x) max acc nat-remove-dups-stobj))
        (t
          (let* ((nat-remove-dups-stobj
                  (update-nat-remove-dups-arri (car x) 1 nat-remove-dups-stobj))
                 (acc (cons (car x) acc)))
            (nat-remove-dups-with-stobj-aux (cdr x) max acc nat-remove-dups-stobj)))))

(defun nat-list-remove-duplicates-exec (x acc)
  ;; Accumulator version of the wrapper.  Guards are verified below.
  ;; Note: we leave this enabled.
  (declare (xargs :guard (nat-listp x) :verify-guards nil))
  (mbe :logic
       (revappend (hons-remove-duplicates x) acc)
       :exec
       (b* (((when (nat-remove-dups-very-short-p x))
             (if acc
                 (nat-remove-dups-when-very-short x acc nil)
               (nat-remove-dups-when-very-short-solo x nil)))

            (max (max-nat x))

            (len-if-needed (if (< max (ash 1 17))
                               nil
                             (length x)))

            (use-array-p
             (or (not len-if-needed)
                 (> len-if-needed (ash max -9))))

            ((when use-array-p)
             (with-local-stobj
              nat-remove-dups-stobj
              (mv-let (acc nat-remove-dups-stobj)
                (b* ((nat-remove-dups-stobj
                      (resize-nat-remove-dups-arr (+ 1 max) nat-remove-dups-stobj))
                     ((mv acc nat-remove-dups-stobj)
                      (nat-remove-dups-with-stobj-aux x max acc nat-remove-dups-stobj)))
                  (mv acc nat-remove-dups-stobj))
                acc)))

            ;; Else, too sparse to use an array.

            ((when (< len-if-needed 350))
             ;; Not enough to warrant a hash table; use the naive algorithm.
             ;; See the tests at the bottom of this file for motivation for the
             ;; number 350.
             (if acc
                 (nat-remove-dups-when-very-short x acc nil)
               (nat-remove-dups-when-very-short-solo x nil))))

         ;; Else, long enough to use a hash table.  We use the length of the
         ;; list as a size hint.  This might mean that we allocate a lot more
         ;; memory than we need (if the list has a lot of duplicates), but it
         ;; should ensure that we won't need to grow the hash table during the
         ;; computation, which could be expensive.

         (hons-remove-duplicates1-tail x len-if-needed acc))))

(defun nat-list-remove-duplicates (x)
  (declare (xargs :guard (nat-listp x) :verify-guards nil))
  (mbe :logic
       (revappend (hons-remove-duplicates x) nil)
       :exec
       (nat-list-remove-duplicates-exec x nil)))



(local
 (defsection alist-and-stobj-agree

   (defun-sk alist-and-stobj-agree (al st)
     (forall key
             (implies (and (natp key)
                           (< key (nat-remove-dups-arr-length st)))
                      (iff (hons-assoc-equal key al)
                           (= 1 (nat-remove-dups-arri key st))))))

   (local (defthmd l0
            (implies
             (and (alist-and-stobj-agree al st)
                  (natp k)
                  (< k (nat-remove-dups-arr-length st)))
             (implies (and (natp key)
                           (< key (nat-remove-dups-arr-length st)))
                      (iff (hons-assoc-equal key (cons (cons k t) al))
                           (= 1 (nat-remove-dups-arri key (update-nat-remove-dups-arri k 1 st))))))
            :hints(("Goal"
                    :in-theory (disable alist-and-stobj-agree-necc)
                    :use ((:instance alist-and-stobj-agree-necc
                                     (key key)
                                     (al al)
                                     (st st)))))))

   (defthm alist-and-stobj-still-agree-after-extension
     (implies (and (alist-and-stobj-agree al st)
                   (force (natp k))
                   (force (< k (nat-remove-dups-arr-length st))))
              (alist-and-stobj-agree (cons (cons k t) al)
                                     (update-nat-remove-dups-arri k 1 st)))
     :hints(("goal"
             :use ((:instance alist-and-stobj-agree
                              (al (cons (cons k t) al))
                              (st (update-nat-remove-dups-arri k 1 st)))
                   (:instance l0
                              (key (alist-and-stobj-agree-witness
                                    (cons (cons k t) al)
                                    (update-nat-remove-dups-arri k 1 st))))))))

   (defthm alist-and-stobj-agree-consequence
     (implies (and (alist-and-stobj-agree al st)
                   (force (natp key))
                   (force (< key (nat-remove-dups-arr-length st))))
              (iff (hons-assoc-equal key al)
                   (= 1 (nat-remove-dups-arri key st))))
     :hints(("Goal"
             :in-theory (disable alist-and-stobj-agree-necc)
             :use ((:instance alist-and-stobj-agree-necc)))))

   (in-theory (disable alist-and-stobj-agree))))



(local
 (defsection nat-remove-dups-with-stobj-aux-elim

   (local
    (defun-nx my-induct (x max acc st al)
      (if (atom x)
          (mv al st)
        (if (= 1 (the (unsigned-byte 1) (nat-remove-dups-arri (car x) st)))
            (my-induct (cdr x) max acc st al)
          (my-induct (cdr x) max
                     (cons (car x) acc)
                     (update-nat-remove-dups-arri (car x) 1 st)
                     (hons-acons (car x) t al))))))

   ;; Main theorem saying that our stobj function is the same as
   ;; hons-remove-duplicates1.
   (defthm nat-remove-dups-with-stobj-aux-elim
     (implies (and (force (nat-listp x))
                   (force (natp max))
                   (force (<= (max-nat x) max))
                   (force (< max (nat-remove-dups-arr-length st)))
                   (force (alist-and-stobj-agree al st)))
              (equal (mv-nth 0 (nat-remove-dups-with-stobj-aux x max acc st))
                     (revappend (hons-remove-duplicates1 x al) acc)))
     :hints(("Goal"
             :induct (my-induct x max acc st al)
             :in-theory (enable nat-remove-dups-with-stobj-aux
                                hons-remove-duplicates1))))))


(local
 (defthm nat-remove-dups-with-stobj-aux-when-atom
   (implies (atom x)
            (equal (nat-remove-dups-with-stobj-aux x max acc st)
                   (mv acc st)))
   :hints(("Goal" :in-theory (enable nat-remove-dups-with-stobj-aux)))))

(local
 (defthm base-case
   (implies (and (atom al)
                 (natp n))
            (let ((st (resize-nat-remove-dups-arr n (create-nat-remove-dups-stobj))))
              (alist-and-stobj-agree al st)))
   :hints(("Goal" :use ((:instance alist-and-stobj-agree
                                   (al al)
                                   (st (resize-nat-remove-dups-arr
                                        n (create-nat-remove-dups-stobj)))))))))



(local
 (defsection hons-remove-duplicates1-atom-irrelevance

   (local (include-book "centaur/misc/alist-equiv" :dir :system))
   (local (in-theory (enable hons-remove-duplicates1)))

   (local (defun my-induct (x tab1 tab2)
            (if (atom x)
                t
              (if (or (hons-get (car x) tab1)
                      (hons-get (car x) tab2))
                  (my-induct (cdr x) tab1 tab2)
                (my-induct (cdr x)
                           (hons-acons (car x) t tab1)
                           (hons-acons (car x) t tab2))))))

   (local (defcong alist-equiv equal (hons-remove-duplicates1 x tab) 2
            :hints(("Goal"
                    :in-theory (enable hons-duplicates1)
                    :induct (my-induct x tab tab-equiv)))))

   (local (defthm crock
            (implies (and (atom x)
                          (atom y))
                     (alist-equiv x y))
            :rule-classes nil
            :hints(("Goal" :in-theory (enable alist-equiv sub-alistp alists-agree)))))

   (defthm hons-remove-duplicates1-atom-irrelevance
     (implies (and (syntaxp (not (equal tab ''nil)))
                   (atom tab))
              (equal (hons-remove-duplicates1 x tab)
                     (hons-remove-duplicates1 x nil)))
     :hints(("Goal"
             :use ((:instance crock (x tab) (y nil)))
             :in-theory (disable hons-remove-duplicates1))))))

(verify-guards nat-list-remove-duplicates-exec
  :hints(("Goal"
          :in-theory (e/d (hons-remove-duplicates1-of-nil)
                          (max-nat))
          :restrict ((nat-remove-dups-with-stobj-aux-elim
                      ((al '*hons-remove-duplicates*)))))))

(verify-guards nat-list-remove-duplicates)



#||

(include-book
 "nat-list-duplicates")
(include-book
 "centaur/misc/memory-mgmt-raw" :dir :system)
(include-book
 "defsort/uniquep" :dir :system)
(include-book
 "defsort/remove-dups" :dir :system)
(include-book
 "finite-set-theory/osets/sets" :dir :system)


(set-max-mem  ;; newline to fool limits scanner
 (* 32 (expt 2 30)))



(defun test (lst times)
  (gc$)

;  (time$ (loop for i fixnum from 1 to times do
;               (nat-list-remove-duplicates lst))
;         :msg "; nat-list-remove-duplicates:   ~st sec, ~sa bytes~%")

; I'm not testing remove-duplicates because it's consistently slower than
; remove-duplicates-eql (which isn't surprising, since it can operate on
; strings in addition to lists.)

;  (time$ (loop for i fixnum from 1 to times do
;               (remove-duplicates lst))
;         :msg "remove-duplicates:              ~st sec, ~sa bytes~%")

  (time$ (loop for i fixnum from 1 to times do
               (remove-duplicates-eql-exec lst))
         :msg "; remove-duplicates-eql:        ~st sec, ~sa bytes~%")

  (time$ (loop for i fixnum from 1 to times do
               (nat-remove-dups-when-very-short-solo lst nil))
         :msg "; naive-solo                    ~st sec, ~sa bytes~%")

  (time$ (loop for i fixnum from 1 to times do
               (nat-remove-dups-when-very-short lst nil nil))
         :msg "; naive-non-solo                ~st sec, ~sa bytes~%")

;  (time$ (loop for i fixnum from 1 to times do
;              (remove-dups lst))
;         :msg "; osets/mergesort:              ~st sec, ~sa bytes~%")
;  (time$ (loop for i fixnum from 1 to times do
;              (remove-dups lst))
;         :msg "; defsort/remove-dups:          ~st sec, ~sa bytes~%")

  (time$ (loop for i fixnum from 1 to times do
               (hons-remove-duplicates lst))
         :msg "; hons-remove-duplicates:       ~st sec, ~sa bytes~%")))



;;; Short lists

(test (loop for i from 1 to 1 collect i) 10000000)

; nat-list-remove-duplicates:   0.24 sec, 160,001,936 bytes
; remove-duplicates-eql:        0.16 sec, 160,001,280 bytes
; osets/mergesort:              0.27 sec, 320,001,280 bytes
; defsort/remove-dups:          0.28 sec, 320,001,280 bytes
; hons-remove-duplicates:       30.23 sec, 17,600,001,280 bytes

(test (loop for i from 1 to 3 collect i) 10000000)

; nat-list-remove-duplicates:   0.64 sec, 480,001,936 bytes
; remove-duplicates-eql:        0.72 sec, 480,001,280 bytes
; osets/mergesort:              2.03 sec, 1,600,001,280 bytes
; defsort/remove-dups:          2.04 sec, 1,600,001,280 bytes
; hons-remove-duplicates:       39.15 sec, 18,560,001,280 bytes

(test (loop for i from 1 to 5 collect i) 10000000)

; nat-list-remove-duplicates:   1.53 sec, 800,001,936 bytes
; remove-duplicates-eql:        1.69 sec, 800,001,280 bytes
; osets/mergesort:              4.21 sec, 3,200,001,280 bytes
; defsort/remove-dups:          4.74 sec, 3,200,001,280 bytes
; hons-remove-duplicates:       50.65 sec, 19,520,001,280 bytes

(test (loop for i from 1 to 10 collect i) 1000000)

; nat-list-remove-duplicates:   0.40 sec, 160,001,936 bytes
; remove-duplicates-eql:        0.43 sec, 160,001,280 bytes
; osets/mergesort:              1.08 sec, 800,001,280 bytes
; defsort/remove-dups:          1.09 sec, 800,001,280 bytes
; hons-remove-duplicates:       6.36 sec, 2,192,001,280 bytes

(test (loop for i from 1 to 15 collect i) 1000000)

; nat-list-remove-duplicates:   0.77 sec, 240,001,936 bytes
; remove-duplicates-eql:        0.83 sec, 240,001,280 bytes
; osets/mergesort:              1.93 sec, 1,376,001,280 bytes
; defsort/remove-dups:          1.91 sec, 1,376,001,280 bytes
; hons-remove-duplicates:       8.58 sec, 2,432,001,280 bytes


;;; Medium Lists

(test (loop for i from 1 to 20 collect i) 1000000)

; nat-list-remove-duplicates:   0.87 sec, 416,001,936 bytes
; remove-duplicates-eql:        1.31 sec, 320,001,280 bytes
; osets/mergesort:              2.56 sec, 1,920,001,280 bytes
; defsort/remove-dups:          2.56 sec, 1,920,001,280 bytes
; hons-remove-duplicates:       10.97 sec, 2,672,001,280 bytes

(test (loop for i from 1 to 30 collect i) 1000000)

; nat-list-remove-duplicates:   1.17 sec, 576,001,936 bytes
; remove-duplicates-eql:        2.61 sec, 480,001,280 bytes
; osets/mergesort:              4.33 sec, 3,232,001,280 bytes
; defsort/remove-dups:          4.69 sec, 3,232,001,280 bytes
; hons-remove-duplicates:       16.84 sec, 3,152,001,280 bytes

(test (loop for i from 1 to 100 collect i) 300000)

; nat-list-remove-duplicates:   0.96 sec, 513,601,936 bytes
; remove-duplicates-eql:        7.18 sec, 480,001,280 bytes
; osets/mergesort:              5.13 sec, 3,993,601,280 bytes
; defsort/remove-dups:          6.55 sec, 3,993,601,280 bytes
; hons-remove-duplicates:       19.81 sec, 3,604,801,280 bytes

(test (loop for i from 1 to 200 collect i) 100000)

; nat-list-remove-duplicates:   0.62 sec, 332,801,936 bytes
; remove-duplicates-eql:        9.14 sec, 320,001,280 bytes
; osets/mergesort:              3.77 sec, 2,982,401,280 bytes
; defsort/remove-dups:          3.79 sec, 2,982,401,280 bytes
; hons-remove-duplicates:       12.53 sec, 2,166,401,280 bytes

(test (append (loop for i from 1 to 200 collect i)
              (loop for i from 1 to 200 collect i))
      100000)


;;; Longer Lists

; nat-list-remove-duplicates:   0.89 sec, 345,601,936 bytes
; remove-duplicates-eql:        27.02 sec, 321,601,280 bytes
; osets/mergesort:              9.38 sec, 6,952,001,280 bytes
; defsort/remove-dups:          12.62 sec, 6,952,001,280 bytes
; hons-remove-duplicates:       14.38 sec, 2,171,201,280 bytes

(test (append (loop for i from 1000 to 1200 collect i)
              (loop for i from 1000 to 1200 collect i))
      100000)

; nat-list-remove-duplicates:   0.90 sec, 345,601,936 bytes
; remove-duplicates-eql:        27.03 sec, 321,601,280 bytes
; osets/mergesort:              9.22 sec, 6,952,001,280 bytes
; defsort/remove-dups:          12.78 sec, 6,952,001,280 bytes
; hons-remove-duplicates:       14.56 sec, 2,171,201,280 bytes

(test (append (loop for i from 1000 to 1200 collect (+ (expt 2 18) i))
              (loop for i from 1000 to 1200 collect (+ (expt 2 18) i)))
      100000)

; nat-list-remove-duplicates:   12.17 sec, 1,916,801,936 bytes
; remove-duplicates-eql:        27.03 sec, 321,601,280 bytes
; osets/mergesort:              10.15 sec, 6,952,001,280 bytes
; defsort/remove-dups:          12.80 sec, 6,952,001,280 bytes
; hons-remove-duplicates:       14.44 sec, 2,171,201,280 bytes


(test (append (loop for i from 1000 to 1200 collect (+ (expt 2 61) i))
              (loop for i from 1000 to 1200 collect (+ (expt 2 61) i)))
      10000)

; nat-list-remove-duplicates:   1.48 sec, 191,841,936 bytes
; remove-duplicates-eql:        4.57 sec, 32,161,280 bytes
; osets/mergesort:              2.03 sec, 695,201,280 bytes
; defsort/remove-dups:          2.03 sec, 695,201,280 bytes
; hons-remove-duplicates:       1.38 sec, 217,121,280 bytes



;;; Really long tests.  You have to take out remove-duplicates-eql
;;; for these.

(test (loop for i from 1 to (expt 2 19) collect i) 100)

; nat-list-remove-duplicates:   2.10 sec, 845,425,936 bytes
; osets/mergesort:              28.33 sec, 17,616,078,080 bytes
; defsort/remove-dups:          34.83 sec, 17,616,078,736 bytes   ( 4.51 sec gc)
; hons-remove-duplicates:       52.08 sec, 7,164,372,480 bytes



;; Figuring a good tipping point from naive -> hash tables when the
;; list contains large elements.

(test (loop for i from 1 to 100 collect (+ (expt 2 19) i)) 100000)

;; naive still winning at length 100:

; remove-duplicates-eql:        2.41 sec, 160,001,936 bytes
; naive-solo                    2.35 sec, 160,001,280 bytes
; naive-non-solo                2.39 sec, 320,001,280 bytes
; hons-remove-duplicates:       5.99 sec, 1,201,601,280 bytes


(test (loop for i from 1 to 200 collect (+ (expt 2 19) i)) 100000)

;; naive still winning (barely) at length 200:

; remove-duplicates-eql:        9.13 sec, 320,001,936 bytes
; naive-solo                    9.01 sec, 320,001,280 bytes
; naive-non-solo                9.09 sec, 640,001,280 bytes
; hons-remove-duplicates:       11.48 sec, 2,166,401,280 bytes


(test (loop for i from 1 to 300 collect (+ (expt 2 19) i)) 20000)

;; naive is losing at 300, but memory allocation is still nice

; remove-duplicates-eql:        4.04 sec, 96,001,936 bytes
; naive-solo                    4.00 sec, 96,001,280 bytes
; naive-non-solo                4.03 sec, 192,001,280 bytes
; hons-remove-duplicates:       3.52 sec, 672,961,280 bytes

(test (loop for i from 1 to 400 collect (+ (expt 2 19) i)) 10000)

;; naive losing worse at length 400, but lower memory-allocation is still possibly worthwhile

; remove-duplicates-eql:        3.57 sec, 64,001,936 bytes
; naive-solo                    3.54 sec, 64,001,280 bytes
; naive-non-solo                3.55 sec, 128,001,280 bytes
; hons-remove-duplicates:       2.46 sec, 491,521,280 bytes




||#
