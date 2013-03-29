; Low level memory management utilities
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(set-state-ok t)

(defdoc Memory
  ":Doc-Section Memory
Memory management utilities.~/~/~/")


(defun mem-get-used-bytes (state)
  ":Doc-Section Memory
How much heap space is currently used.~/

~bv[]
 (mem-get-used-bytes) -> (mv er bytes state)
~ev[]

~c[er] is always a Boolean; ~c[bytes] is always a natural.

Logically this is just an oracle read.

We try to determine how heap space is currently in use.  This measure is
somewhat arbitrary, e.g., on CCL we only return the ``dynamic'' usage without
accounting for other kinds of memory (e.g., ``static'', ``library'', and
``frozen'' memory).  On success, ~c[er] is ~c[nil] and this amount of space is
returned as ~c[bytes].

We may fail, e.g., due to an unsupported Lisp; in this case ~c[er] is ~c[t] and
~c[bytes] is just set to ~c[0].~/~/"

  (declare (xargs :guard t :stobjs state))
  (mv-let (er val state)
    (read-acl2-oracle state)
    (mv er (nfix val) state)))

(defthm booleanp-of-mem-get-used-bytes.er
  (booleanp (mv-nth 0 (mem-get-used-bytes state)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable read-acl2-oracle))))

(defthm natp-of-mem-get-used-bytes.bytes
  (natp (mv-nth 1 (mem-get-used-bytes state)))
  :rule-classes :type-prescription)


(defun mem-get-free-bytes (state)
  ":Doc-Section Memory
How much heap space is currently free, i.e., how long until the next GC.~/

~bv[]
 (mem-get-free-bytes) -> (mv er bytes state)
~ev[]

~c[er] is always a Boolean; ~c[bytes] is always a natural.

Logically this is just an oracle read.

We try to determine how heap space is currently allocated and available.  This
may roughly indicate how much we can allocate before the next GC will be
triggered (except that schemes like ephemeral garbage collection can complicate
the story).

On success, ~c[er] is ~c[nil] and this amount of space is returned as
~c[bytes].

We may fail, e.g., due to an unsupported Lisp; in this case ~c[er] is ~c[t] and
~c[bytes] is just set to ~c[0].~/~/"

  (declare (xargs :guard t :stobjs state))
  (mv-let (er val state)
    (read-acl2-oracle state)
    (mv er (nfix val) state)))

(defthm booleanp-of-mem-get-free-bytes.er
  (booleanp (mv-nth 0 (mem-get-free-bytes state)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable read-acl2-oracle))))

(defthm natp-of-mem-get-free-bytes.bytes
  (natp (mv-nth 1 (mem-get-free-bytes state)))
  :rule-classes :type-prescription)



(defun mem-get-gc-threshold (state)
  ":Doc-Section Memory
How much free space will be left in the heap after each GC.~/

~bv[]
 (mem-get-gc-threshold) -> (mv er bytes state)
~ev[]

~c[er] is always a Boolean; ~c[bytes] is always a natural.

Logically this is just an oracle read.

We try to determine how much free space the Lisp wants to leave in the heap
after a garbage collection.  On success, ~c[er] is ~c[nil] and this amount of
free space is returned as ~c[bytes].

We may fail, e.g., due to an unsupported Lisp; in this case ~c[er] is ~c[t] and
~c[bytes] is just set to ~c[0].~/~/"

  (declare (xargs :guard t :stobjs state))
  (mv-let (er val state)
    (read-acl2-oracle state)
    (mv er (nfix val) state)))

(defthm booleanp-of-mem-get-gc-threshold.er
  (booleanp (mv-nth 0 (mem-get-gc-threshold state)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable read-acl2-oracle))))

(defthm natp-of-mem-get-gc-threshold.bytes
  (natp (mv-nth 1 (mem-get-gc-threshold state)))
  :rule-classes :type-prescription)



(defun mem-set-gc-threshold (bytes)
  ":Doc-Section Memory
Set how much free space to leave in the heap after each GC.~/

~bv[]
 (mem-set-gc-threshold bytes) -> nil
~ev[]

Logically this does nothing.

In the execution, on supported Lisps, we try to set up how much free space to
keep in the heap after a garbage collection.

~st[Note:] just setting this threshold won't have any immediate effect on how
much memory your Lisp is using.  It governs how much free space to leave afqter
the ~em[next] garbage collection.  But see also ~ilc[mem-use-gc-threshold].

On unsupported Lisps, this just does nothing.~/~/"
  (declare (xargs :guard (natp bytes))
           (ignorable bytes))
  nil)



(defun mem-use-gc-threshold ()
  ":Doc-Section Memory
Try to grow or shrink the current heap to have the desired amount of
free space available.~/

~bv[]
 (mem-use-gc-threshold) -> nil
~ev[]

Logically this does nothing.

In the execution, on supported Lisps, we try to adjust the current amount of
free space in the heap to match the desired threshold.  See
~il[mem-get-gc-threshold] and ~il[mem-set-gc-threshold].

On unsupported Lisps, this just does nothing.~/~/"

  (declare (xargs :guard t))
  nil)



(defun mem-get-egc (state)
  ":Doc-Section Memory
Try to determine whether ephemeral garbage collection is enabled.~/

~bv[]
 (mem-get-egc) -> (mv er enabled-p state)
~ev[]

~c[er] and ~c[enabled-p] are always Booleans.

Logically this is just an oracle read.

We try to determine if ephemeral garbage collection is enabled.  On success,
~c[er] is ~c[nil] and ~c[enabled-p] is the answer.

On unsupported Lisps, we just set ~c[er] to ~c[t] and arbitrarily say that
~c[enabled-p] is ~c[nil].~/~/"

  (declare (xargs :guard t :stobjs state))
  (mv-let (er val state)
    (read-acl2-oracle state)
    (mv er (if val t nil) state)))

(defthm booleanp-of-mem-get-egc.er
  (booleanp (mv-nth 0 (mem-get-egc state)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable read-acl2-oracle))))

(defthm booleanp-of-mem-get-egc.egc-p
  (booleanp (mv-nth 1 (mem-get-egc state)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable read-acl2-oracle))))


(defun mem-set-egc (enabled-p)
  ":Doc-Section Memory
Try to enable or disable ephemeral garbage collection.~/

~bv[]
 (mem-set-egc enabled-p) -> nil
~ev[]

Logically this does nothing.

In the execution, on supported Lisps, this tries to turn on or off ephemeral
garbage collection.

On unsupported Lisps, this just does nothing.~/~/"

  (declare (xargs :guard (booleanp enabled-p))
           (ignore enabled-p))
  nil)


(defdoc mem-gc-hook
  ":Doc-Section Memory
Hook for triggering actions after garbage collection.~/

~bv[]
 (mem-gc-hook state) => state
~ev[]

This is a special, attachable function that, on supported Lisps, is called
shortly after garbage collection occurs.  It can be used to implement various
garbage collection strategies using ~il[memory] related functions.

Note that this function can be run ``at random'', as dictated by the whims of
the garbage collector.  Because of this, it has a special, very restrictive
constraint: it is only allowed to modify the ~c[oracle] field of the state, and
must leave all other fields alone.~/~/")

(encapsulate
  ()
  (local (defthm len-when-state-p1
           (implies (state-p1 x)
                    (equal (len x) 15))
           :hints(("Goal" :in-theory (enable state-p1)))))

  (local (defthm update-nth-same
           (implies (< (nfix n) (len x))
                    (equal (update-nth n (nth n x) x)
                           x))))

  (defthm mem-gc-hook-lemma
    (implies (state-p1 state)
             (equal (update-acl2-oracle (nth 7 state) state)
                    state))
    :hints(("Goal" :in-theory (enable update-acl2-oracle)))))

(encapsulate
  (((mem-gc-hook state) => state))
  (local (defun mem-gc-hook (state)
           (declare (xargs :stobjs state))
           state))

  (defthm mem-gc-hook-constraint
    (implies
     (state-p1 state)
     (let* ((post-state        (mem-gc-hook state))
            (post-state-oracle (acl2-oracle post-state)))
       (equal (update-acl2-oracle post-state-oracle state)
              post-state)))
    :rule-classes nil))


(defun empty-gc-hook (state)
  ":Doc-Section Memory
The default ~il[mem-gc-hook].~/

~bv[]
  (empty-gc-hook state) => state
~ev[]

This just returns the state unchanged.~/~/"
  (declare (xargs :stobjs state))
  state)

(defattach mem-gc-hook empty-gc-hook)

