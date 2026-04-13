; The state of the JVM
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "bindings")
(include-book "values")
(include-book "classes")
(include-book "call-stacks")
(include-book "intern-table")
(include-book "strings")
(include-book "kestrel/utilities/myif" :dir :system)
(include-book "kestrel/alists-light/lookup" :dir :system)
(include-book "kestrel/alists-light/acons" :dir :system)
(include-book "locals")
(include-book "float-to-bits")
(include-book "array-building")
(include-book "kestrel/booleans/bool-fix-def" :dir :system)
(include-book "kestrel/bv/defs-arith" :dir :system)
(include-book "kestrel/bv/bvsx-def" :dir :system)
(include-book "kestrel/bv/defs" :dir :system) ;overkill
(include-book "kestrel/bv/sbvlt-def" :dir :system)
(include-book "kestrel/bv-arrays/bv-arrayp" :dir :system)
(include-book "kestrel/bv-arrays/bv-array-read" :dir :system)
(include-book "kestrel/bv-arrays/bv-array-write" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "kestrel/lists-light/subrange-def" :dir :system)
(include-book "kestrel/lists-light/update-subrange2" :dir :system)
(local (include-book "kestrel/sequences/defforall" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

(defthm intern-table-okp-of-initialize-one-dim-array
  (implies (not (set::in ad (acl2::rkeys heap)))
           (equal (intern-table-okp intern-table (initialize-one-dim-array ad element-type contents heap))
                  (intern-table-okp intern-table heap)))
  :hints (("Goal" :in-theory (enable initialize-one-dim-array))))

(defthm not-memberp-of-remove1-equal-when-no-duplicatesp-equal
  (implies (no-duplicatesp-equal x)
           (not (MEMBERP a (REMOVE1-EQUAL a x)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;
;; The heapref-table:
;;

;; FIXME: can the keys of this be the names of primitive types (and void)?
;;FIXME rename this thing to class-object-table?
;;  The heapref-table is a map from class-nameps (strings) to references to (i.e., heap addresses of) their associated
;; heap objects of class Class (FIXME Logically, could we just search
;; the heap to find the corresponding class object each time?).  These
;; are the objects that get locked for synchronized static methods.

;;FIXME When do the class objects get created?!

;; The JVM spec for INVOKESTATIC says: "If the method is synchronized,
;; the monitor associated with the resolved Class object is entered or
;; reentered as if by execution of a monitorenter instruction
;; (monitorenter) in the current thread."

;fixme: make this an alist instead of a map?

;fixme check that the heap object is in fact right?
(defforall all-heapref-table-entryp (x)
  (and (consp x)
       (class-namep (car x))
       (addressp (cdr x)))
  :declares ((xargs :guard (alistp x))))

(in-theory (disable jvm::use-all-heapref-table-entryp ; a bad rule
                    jvm::use-all-heapref-table-entryp-for-car ; also seems bad
                    ))

;fixme flesh this out:
(defund heapref-tablep (x) (declare (xargs :guard t))
  (and (alistp x)
       (all-heapref-table-entryp x)))

(defund empty-heapref-table () (declare (xargs :guard t)) nil)

(defthm heapref-tablep-of-empty-heapref-table
  (heapref-tablep (empty-heapref-table)))

;; todo: use a custom setter:
(defthm heapref-tablep-of-acons
  (equal (heapref-tablep (acons class-name ad heapref-table))
         (and (heapref-tablep heapref-table)
              (class-namep class-name)
              (addressp ad)))
  :hints (("Goal" :in-theory (enable heapref-tablep acons))))

;; returns an address or nil (error: there should always be a result?)
(defund get-class-object (class-name heapref-table)
  (declare (xargs :guard (and (class-namep class-name)
                              (heapref-tablep heapref-table))))
  (lookup-equal class-name heapref-table))

;drop?
(local
 (defthm addressp-of-lookup-equal-when-heapref-tablep
   (implies (and (heapref-tablep heapref-table)
                 (lookup-equal class-name heapref-table))
            (addressp (lookup-equal class-name heapref-table)))
   :hints (("Goal" :in-theory (enable heapref-tablep)))))

(defthm addressp-of-get-classs-object
  (implies (and (heapref-tablep heapref-table)
                (get-class-object class-name heapref-table) ; the class is present
                )
           (addressp (get-class-object class-name heapref-table)))
  :hints (("Goal" :in-theory (enable get-class-object))))

;;
;; The monitor-table
;;

;; The monitor table is a map from objects to thread-designator/mcount
;; pairs.  It contains an entry for each object whose associated
;; monitor is locked, giving the locking thread and the "mcount" (the
;; number of times the thread has reentered the monitor since acquiring
;; the lock).  We do not store pairs with an mcount of 0; instead, we
;; delete such pairs.

;; Note that M5 stores this information in the heap, which can cause
;; problems.

;; The JVM spec for MONITORENTER says: "The association of a monitor
;; with an object may be managed in various ways that are beyond the
;; scope of this specification. For instance, the monitor may be
;; allocated and deallocated at the same time as the
;; object. Alternatively, it may be dynamically allocated at the time
;; when a thread attempts to gain exclusive access to the object and
;; freed at some later time when no thread remains in the monitor for
;; the object."

;FIXME What about wait, notify, and notifyAll?

;A thread-designatorp is a natural number that names a thread. (We previously
;used :th to name the thread used for single-threaded work; now we use 0.)
; TODO: Rename to thread-id?
(defund thread-designatorp (x)
  (declare (xargs :guard t))
  (natp x))

;so that we don't use the fact that thread-designatorp currently always returns t:
(in-theory (disable thread-designatorp (:type-prescription thread-designatorp)))

;A value of 0 cannot appear for an mcount (instead, we delete the entry from the monitor-table).
(defund mcountp (x)
  (declare (xargs :guard t))
  (posp x))

(defthm mcountp-of-plus-1
  (implies (mcountp x)
           (mcountp (+ 1 x)))
  :hints (("Goal" :in-theory (enable mcountp))))

(defthm mcountp-of-minus-1
  (implies (and (mcountp x)
                (not (equal 1 x)))
           (mcountp (+ -1 x)))
  :hints (("Goal" :in-theory (enable mcountp))))

(defforall all-keys-bound-to-thread-designator-mcount-pairsp (key monitor-table)
;  (let ((pair (g key monitor-table))) ;fixme the let causes a guard violation in the macro...
  (and (consp (g key monitor-table))
       (thread-designatorp (car (g key monitor-table)))
       (mcountp (cdr (g key monitor-table))))
  :declares ((xargs :guard t)
             )
  :fixed monitor-table)

(defund monitor-tablep (monitor-table)
  (declare (xargs :guard t))
  (let* ((dom (acl2::rkeys monitor-table))
         (key-list (SET::2LIST dom))) ;call key-list?
    (and (acl2::all-addressp key-list)
         (all-keys-bound-to-thread-designator-mcount-pairsp key-list monitor-table))))

;; Initially, no objects are locked:
(defund empty-monitor-table () (declare (xargs :guard t)) (acl2::empty-map))

(defthm monitor-tablep-of-empty-monitor-table
  (monitor-tablep (empty-monitor-table))
  :hints (("Goal" :in-theory (enable monitor-tablep empty-monitor-table))))

;fixme abstract better so we don't see the consp
;could be expensive
(defthm consp-of-g-when-monitor-tablep
  (IMPLIES (AND (MONITOR-TABLEP MONITOR-TABLE)
                (SET::IN OBJECTREF (ACL2::RKEYS MONITOR-TABLE)))
           (CONSP (G OBJECTREF MONITOR-TABLE)))
  :hints (("Goal" :in-theory (enable MONITOR-TABLEP))))

(defthm mcountp-of-cdr-of-g-when-monitor-tablep
  (IMPLIES (AND (MONITOR-TABLEP MONITOR-TABLE)
                (SET::IN OBJECTREF (ACL2::RKEYS MONITOR-TABLE)))
           (mcountp (CDR (G OBJECTREF MONITOR-TABLE))))
  :hints (("Goal" :in-theory (enable MONITOR-TABLEP))))

(defun increment-mcount (mcount)
  (declare (xargs :guard (mcountp mcount)))
  (+ 1 mcount))

;returns (successp new-monitor-table) where new-monitor-table is only valid if successp is t
(defund attempt-to-enter-monitor (th objectref monitor-table)
  (declare (xargs :guard (and (monitor-tablep monitor-table)
                              (addressp objectref)))) ;improve?
  (let ((entry (g objectref monitor-table)))
    (if (null entry)
        ;; No thread currently owns the lock:
        (mv t (s objectref (cons th 1) monitor-table))
      ;;Some thread currently owns the lock:
      (let ((owning-thread (car entry)))
        (if (equal owning-thread th)
            ;; This thread already owns the lock, so increment the mcount:
            (let ((mcount (cdr entry)))
              (mv t (s objectref (cons th (increment-mcount mcount)) monitor-table)))
          ;; Another thread owns the lock, so the attempt to enter the monitor fails:
          (mv nil monitor-table))))))

(defthm all-keys-bound-to-thread-designator-mcount-pairsp-of-s-irrel
  (implies (not (memberp key lst))
           (equal (all-keys-bound-to-thread-designator-mcount-pairsp lst (s key val monitor-table))
                  (all-keys-bound-to-thread-designator-mcount-pairsp lst monitor-table)))
  :hints (("Goal" :in-theory (enable all-keys-bound-to-thread-designator-mcount-pairsp))))

(defthm all-keys-bound-to-thread-designator-mcount-pairsp-of-s-not-irrel
  (implies (all-keys-bound-to-thread-designator-mcount-pairsp lst monitor-table)
           (equal (all-keys-bound-to-thread-designator-mcount-pairsp lst (s key val monitor-table))
                  (if (memberp key lst)
                      (and (consp val)
                           (thread-designatorp (car val))
                           (mcountp (cdr val)))
                    t)))
  :hints (("Goal" :in-theory (enable all-keys-bound-to-thread-designator-mcount-pairsp))))

(defthm monitor-tablep-of-mv-nth-1-of-attempt-to-enter-monitor
  (implies (and (monitor-tablep monitor-table)
                (thread-designatorp th)
                (acl2::addressp objectref))
           (monitor-tablep (mv-nth 1 (attempt-to-enter-monitor th objectref monitor-table))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable monitor-tablep ATTEMPT-TO-ENTER-MONITOR))))

(defthm monitor-tablep-of-clear
  (implies (monitor-tablep monitor-table)
           (monitor-tablep (s key nil monitor-table)))
  :hints (("Goal" :in-theory (e/d (monitor-tablep) (;ACL2::S-NIL-BECOMES-CLR
                                                    )))))

;; Check whether thread th owns the lock on objectref.
;could have this check that the mcount is positive, but that is part of monitor-tablep...
(defun thread-owns-monitorp (th objectref monitor-table)
  (declare (xargs :guard (monitor-tablep monitor-table)
                  :guard-hints (("Goal" :in-theory (enable consp-of-g-when-MONITOR-TABLEP)))))
  (let ((entry (g objectref monitor-table)))
    (and entry
         (equal th (car entry)))))

;a helper function with a nicer guard.
(defun decrement-mcount-helper (mcount)
  (declare (xargs :guard (mcountp mcount)))
  (+ -1 mcount))

;returns the new monitor-table
;What if the thread does not actually own the monitor?  You should call thread-owns-monitorp first to check that.
(defund decrement-mcount (objectref monitor-table)
  (declare (xargs :guard (and (monitor-tablep monitor-table)
                              (g objectref monitor-table) ;rephrase?
                              )
                  :guard-hints (("Goal" :in-theory (enable consp-of-g-when-MONITOR-TABLEP)))))
  (let* ((entry (g objectref monitor-table))
         (mcount (cdr entry)))
    (if (eql 1 mcount)
        ;;clear the entry instead of storing an entry with a 0 mcount:
        (s objectref nil monitor-table) ;use a 'clear' function
      (let ((owning-thread (car entry)))
        (s objectref (cons owning-thread (decrement-mcount-helper mcount)) monitor-table)))))

(defthm monitor-tablep-of-decrement-mcount
  (implies (and (acl2::addressp objectref)
                (set::in objectref (acl2::rkeys monitor-table))
                (mcountp (cdr (g objectref monitor-table)))
                (monitor-tablep monitor-table))
           (monitor-tablep (decrement-mcount objectref monitor-table)))
  :hints (("Goal" :in-theory (e/d (monitor-tablep decrement-mcount mcountp) (;ACL2::S-NIL-BECOMES-CLR
                                                                             )))))

;;
;; The static-field-map
;;

;we are no longer storing static fields in the heap (led to aliasing problems)
;instead we store them in this map
;This is a map whose keys are class-name/field-id pairs and whose values are the values of the static fields.
;do these things get mentioned in the class table at all?
;we need to think about how these fields get initialized (maybe that is handled okay now?)

(defund static-field-mapp (x)
  (declare (xargs :guard t))
  (ACL2::MAPP x)
  ) ;todo: flesh this out!

;should not be enabled in proof -- in case we forget to set this right, we don't want to just read from nil..
(defun empty-static-field-map () (declare (xargs :guard t)) (acl2::empty-map))

(defthm static-field-mapp-of-empty-static-field-map
  (static-field-mapp (empty-static-field-map))
  :hints (("Goal" :in-theory (enable static-field-mapp))))

;returns a new static-field-map
(defun set-static-field (class-name field-id value static-field-map)
  (declare (xargs :guard (and (class-namep class-name)
                              (field-idp field-id)
                              (static-field-mapp static-field-map))))
  (s (cons class-name field-id)
     value
     static-field-map))

(defthm static-field-mapp-of-set-static-field
  (implies (and (class-namep class-name)
                (static-field-mapp static-field-map))
           (static-field-mapp (set-static-field class-name field-id value static-field-map)))
  :hints (("Goal" :in-theory (enable static-field-mapp))))

(defund get-static-field (class-name field-id static-field-map)
  (declare (xargs :guard (and (class-namep class-name)
                              (field-idp field-id)
                              (static-field-mapp static-field-map))))
  (let* ((pair (cons class-name field-id))
         (result (acl2::fastg pair static-field-map)))
    result))

;; ;TODO what about the class-name?
;; (defun method-name-and-descriptor-pairp (x)
;;   (declare (xargs :guard t))
;;   (and (consp x)
;;        (method-namep (car x))
;;        (descriptorp (cdr x))))

;; (DEFTHM CDR-IFF-when-len
;;   (IMPLIES (< 1 (LEN X))
;;            (IFF (CDR X)
;;                 t
;;                 ))
;;   :HINTS (("Goal" :EXPAND ((LEN X)))))

;Thread tables:
;FIXME replace most or all uses of this bind/binding alist stuff with map operations?

;fixme abstract out the pattern of typed alists
;could use a defforall
(defun thread-tablep-aux (x)
  (declare (xargs :guard (alistp x)))
  (if (atom x)
      t
    (let ((entry (first x)))
      (and (thread-designatorp (car entry))
           (call-stackp (cdr entry))
           (thread-tablep-aux (rest x))))))

;; The thread-table is an alist mapping thread-designators to call-stacks.
(defund thread-tablep (x)
  (declare (xargs :guard t))
  (and (alistp x)
       (thread-tablep-aux x)))

(defund empty-thread-table () (declare (xargs :guard t)) nil)

(defthm thread-tablep-of-empty-thread-table
  (thread-tablep (empty-thread-table))
  :hints (("Goal" :in-theory (enable empty-thread-table thread-tablep))))

(defthm thread-tablep-of-bind
  (implies (thread-tablep thread-table)
           (equal (thread-tablep (bind th item thread-table))
                  (and (call-stackp item)
                       (thread-designatorp th))))
  :hints (("Goal" :in-theory (enable thread-tablep bind))))

;fixme use lookup-equal?
(defthm call-stackp-of-binding
  (implies (and (bound-in-alistp th thread-table)
                (thread-tablep thread-table)
                (thread-designatorp th))
           (call-stackp (binding th thread-table)))
  :hints (("Goal" :in-theory (enable thread-tablep bound-in-alistp binding))))

;; (defun addto-tt (call-stack status heapRef tt)
;;   (bind (len tt) (list call-stack status heapRef) tt))

; ----------------------------------------------------------------------------
; Helper function for determining if an object is a 'Thread' object

;what if it implements the java.lang.Runnable Interface?
(defund thread-classp (class-name class-table)
  (declare (xargs :guard (and (class-namep class-name)
                              (class-tablep class-table))))
  (let* (;(class-info (get-class-info class-name class-table))
         (psupers (get-superclasses class-name class-table);(class-decl-superclasses class-info)
          )
         (supers (cons class-name psupers)))
    (or (memberp "java.lang.Thread" supers)
        (memberp "java.lang.ThreadGroup" supers) ;why?
        )))


;;
;; JVM states
;;

;FIXME use a record/map for this, or would that be too slow?

(defund jvm-statep (s)
  (declare (xargs :guard t))
  (and (equal (len s) 8)
       (true-listp s)
       (thread-tablep            (nth 0 s))
       (heapp                    (nth 1 s))
       (class-tablep             (nth 2 s))
       (heapref-tablep           (nth 3 s))
       (monitor-tablep           (nth 4 s))
       (static-field-mapp        (nth 5 s))
       (class-name-listp         (nth 6 s))
       (intern-tablep (nth 7 s))
       (intern-table-okp (nth 7 s) (nth 1 s))
       ))

(defthm jvm-statep-forward-to-true-listp
  (implies (jvm-statep s)
           (true-listp s))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable jvm-statep))))

(defund make-state (thread-table
                    heap
                    class-table
                    heapref-table
                    monitor-table
                    static-field-map
                    initialized-class-names
                    intern-table)
  (declare (xargs :guard t)) ;fixme strengthen?!
  (list thread-table heap class-table heapref-table monitor-table static-field-map initialized-class-names intern-table))

(defund empty-state (class-table)
  (declare (xargs :guard t))
  (make-state (empty-thread-table)
              (empty-heap)
              class-table ;(empty-class-table)
              (empty-heapref-table)
              (empty-monitor-table)
              (empty-static-field-map)
              nil ;initialized-class-names
              (empty-intern-table)))

;fixme should these have a guard of jvm-statep?
(defund thread-table        (s) (declare (xargs :guard (true-listp s))) (nth 0 s))
(defund heap                (s) (declare (xargs :guard (true-listp s))) (nth 1 s))
(defund class-table         (s) (declare (xargs :guard (true-listp s))) (nth 2 s))
(defund heapref-table       (s) (declare (xargs :guard (true-listp s))) (nth 3 s))
(defund monitor-table       (s) (declare (xargs :guard (true-listp s))) (nth 4 s))
(defund static-field-map    (s) (declare (xargs :guard (true-listp s))) (nth 5 s))
;;fixme rename to initialized-class-names
(defund initialized-classes (s) (declare (xargs :guard (true-listp s))) (nth 6 s))
(defund intern-table        (s) (declare (xargs :guard (true-listp s))) (nth 7 s))

;recharacterize the state to use the nice state component accessors:
(defthmd jvm-statep-def
 (equal (jvm-statep s)
        (and (equal (len s) 8)
             (true-listp s)
             (thread-tablep            (thread-table s))
             (heapp                    (heap s))
             (class-tablep             (class-table s))
             (heapref-tablep           (heapref-table s))
             (monitor-tablep           (monitor-table s))
             (static-field-mapp        (static-field-map s))
             (class-name-listp         (initialized-classes s))
             (intern-tablep            (intern-table s))
             (intern-table-okp (intern-table s) (heap s))
             ))
 :rule-classes (:rewrite ; do I need this?
                :definition)
 :hints (("Goal" :in-theory (enable jvm-statep thread-table heap class-table heapref-table monitor-table static-field-map initialized-classes intern-table))))

(defthm thread-table-of-make-state
  (equal (thread-table (make-state tt h c hrt monitor-table sfm ic intern-table))
         tt)
  :hints (("Goal" :in-theory (enable make-state thread-table))))

(defthm heap-of-make-state
  (equal (heap (make-state tt h c hrt monitor-table sfm ic intern-table))
         h)
  :hints (("Goal" :in-theory (enable make-state heap))))

(defthm class-table-of-make-state
  (equal (class-table (make-state tt h c hrt monitor-table sfm ic intern-table))
         c)
  :hints (("Goal" :in-theory (enable make-state class-table))))

(defthm heapref-table-of-make-state
  (equal (heapref-table (make-state tt h c hrt monitor-table sfm ic intern-table))
         hrt)
  :hints (("Goal" :in-theory (enable make-state heapref-table))))

(defthm monitor-table-of-make-state
  (equal (monitor-table (make-state tt h c hrt monitor-table sfm ic intern-table))
         monitor-table)
  :hints (("Goal" :in-theory (enable make-state monitor-table))))

(defthm static-field-map-of-make-state
  (equal (static-field-map (make-state tt h c hrt monitor-table sfm ic intern-table))
         sfm)
  :hints (("Goal" :in-theory (enable make-state static-field-map))))

(defthm initialized-classes-of-make-state
  (equal (initialized-classes (make-state tt h c hrt monitor-table sfm ic intern-table))
         ic)
  :hints (("Goal" :in-theory (enable make-state initialized-classes))))

(defthm intern-table-of-make-state
  (equal (intern-table (make-state tt h c hrt monitor-table sfm ic intern-table))
         intern-table)
  :hints (("Goal" :in-theory (enable make-state intern-table))))

(defthm len-of-make-state
  (equal (len (make-state thread-table heap class-table hrt monitor-table sfm ic intern-table))
         8)
  :hints (("Goal" :in-theory (enable make-state))))

(defthm jvm-statep-of-make-state
  (equal (jvm-statep (make-state thread-table heap class-table hrt monitor-table sfm ic intern-table))
         (and (thread-tablep thread-table)
              (heapp heap)
              (class-tablep class-table)
              (heapref-tablep hrt)
              (monitor-tablep monitor-table)
              (static-field-mapp sfm)
              (class-name-listp ic)
              (intern-tablep intern-table)
              (intern-table-okp intern-table heap)))
  :hints (("Goal" :in-theory (enable jvm-statep make-state))))

(defthm thread-tablep-of-thread-table
  (implies (jvm-statep s)
           (thread-tablep (thread-table s)))
  :hints (("Goal" :in-theory (enable jvm-statep thread-table))))

;fixme more like this

(defthm monitor-tablep-of-monitor-table
  (implies (jvm-statep s)
           (monitor-tablep (monitor-table s)))
  :hints (("Goal" :in-theory (enable jvm-statep monitor-table))))

(defthm class-tablep-of-class-table
  (implies (jvm-statep s)
           (class-tablep (class-table s)))
  :hints (("Goal" :in-theory (enable jvm-statep class-table))))

(defthm class-tablep0-of-class-table
  (implies (jvm-statep s)
           (class-tablep0 (class-table s)))
  :hints (("Goal" :in-theory (enable jvm-statep class-table))))

(defthm static-field-mapp-of-static-field-map
  (implies (jvm-statep s)
           (static-field-mapp (static-field-map s)))
  :hints (("Goal" :in-theory (enable jvm-statep static-field-map))))

(defthm heapp-of-heap
  (implies (jvm-statep s)
           (heapp (heap s)))
  :hints (("Goal" :in-theory (enable jvm-statep heap))))

(defthm heapref-tablep-of-heapref-table
  (implies (jvm-statep s)
           (heapref-tablep (heapref-table s)))
  :hints (("Goal" :in-theory (enable jvm-statep heapref-table))))

(defthm intern-tablep-of-intern-table
  (implies (jvm-statep s)
           (intern-tablep (intern-table s)))
  :hints (("Goal" :in-theory (enable jvm-statep intern-table))))

(defthm intern-table-okp-of-intern-table-and-heap
  (implies (jvm-statep s)
           (intern-table-okp (intern-table s) (heap s)))
  :hints (("Goal" :in-theory (enable jvm-statep intern-table heap))))

;drop?
(defthm addressp-of-lookup-equal-of-heapref-table
  (implies (and (jvm-statep s)
                (lookup-equal class-name (heapref-table s)))
           (addressp (lookup-equal class-name (heapref-table s)))))

(defthm class-name-listp-of-initialized-classes
  (implies (jvm-statep s)
           (class-name-listp (initialized-classes s)))
  :hints (("Goal" :in-theory (enable jvm-statep initialized-classes))))

(defthm alistp-when-thread-tablep-special-case
  (implies (thread-tablep (thread-table s))
           (alistp (thread-table s))))

;to be left enabled.  fixme drop?
(defun call-stack (th s)
  (declare (xargs :guard (and (thread-designatorp th)
                              (jvm-statep s)
                              (bound-in-alistp th (thread-table s)))))
  (binding th (thread-table s)))

;; (thm
;;  (IMPLIES (AND (BOUND-IN-ALISTP TH (THREAD-TABLE S))
;;                (JVM-STATEP S)
;;                (THREAD-DESIGNATORP TH))
;;           (STACKP (GET-CALL-STACK (BINDING TH (THREAD-TABLE S)))))
;;  :hints (("Goal" :in-theory (enable JVM-STATEP))))

;fixme decide whether to keep this open or closed..
(defun thread-top-frame (th s)
  (declare (xargs :guard (and (thread-designatorp th)
                              (jvm-statep s)
                              (bound-in-alistp th (thread-table s)))))
  (top-frame (call-stack th s)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; To model various errors, we use the function ERROR-STATE, about which very little is known.  Simulation
;can't continue when error-state is encountered, and so we'll have to add hyps
;sufficient to exclude such cases.  the msg parameter of error-state
;can be used to pass more info (such as the index and array reference when an
;ArrayIndexOutOfBoundsException exception is thrown) - to aid in debugging (the message will show up in failed proofs).
;FIXME make sure we check exceptions for all relevant array instructions (of all different types)

;;Previously error-state returned s, but the user might be able to cheat by
;;opening that up (perhaps showing that erroneous computations loop forever --
;;and thus are partially correct)

(encapsulate
 (((error-state * *) => *))

 ;; Local witness for the encapsulate:
 (local (defun error-state (msg s)
          (declare (ignore msg s))
          (empty-state (empty-class-table))))

 (defthm jvm-statep-of-error-state
   (implies (jvm-statep s)
            (jvm-statep (error-state msg s)))
   :hints (("Goal" :in-theory (enable error-state))))

 ;; Helps with the symbolic-execution machinery, because calls to
 ;; step-state-with-pc-and-call-stack-height can be shown to usually do nothing
 ;; to an error state.
 (defthm call-stack-size-of-binding-of-thread-table-of-error-state
   (equal (call-stack-size (binding th (thread-table (error-state msg s))))
          0)
   :hints (("Goal" :in-theory (enable binding)))))

;returns a (mv error-message monitor-table) where if error-message is non-nil it indicates an error and is a list of messages, etc. for the call of error-state
;pass in the instruction for debugging?
;;FIXME Think about structured locking.
;FIXME add real exceptions..
(defund attempt-to-exit-monitor (th objectref monitor-table)
  (if (null-refp objectref)
      (mv (list *NullPointerException* 'attempt-to-exit-monitor)
          monitor-table)
    (if (not (thread-owns-monitorp th objectref monitor-table))
        (mv (list *IllegalMonitorStateException* 'attempt-to-exit-monitor)
            monitor-table)
      (mv nil ;no error
          (decrement-mcount objectref monitor-table)))))

(defthm monitor-tablep-of-mv-nth-1-of-attempt-to-exit-monitor
  (implies (monitor-tablep monitor-table)
           (monitor-tablep (mv-nth 1 (attempt-to-exit-monitor th objectref monitor-table))))
  :hints (("Goal" :in-theory (e/d (attempt-to-exit-monitor monitor-tablep decrement-mcount) (;ACL2::S-NIL-BECOMES-CLR
                                                                                             )))))


(defthm thread-top-frame-of-make-state-of-bind
  (equal (thread-top-frame th (make-state (bind th cs tt) h ct hrt monitor-table sfm ic intern-table))
         (top-frame cs)
         )
  :hints (("Goal" :in-theory (enable thread-top-frame call-stack make-state thread-table))))

(defun call-stack-non-emptyp (th s)
  (declare (xargs :guard (and (thread-designatorp th)
                              (jvm-statep s)
                              (bound-in-alistp th (thread-table s)))))
  (not (empty-call-stackp (call-stack th s))))

;; (thm
;;  (IMPLIES (AND (CONSP (GET-CALL-STACK (BINDING TH thread-table)))
;;                (BOUND-IN-ALISTP TH thread-table)
;;                (THREAD-TABLEP thread-table)
;;                (THREAD-DESIGNATORP TH))
;;           (FRAMEP (CAR (GET-CALL-STACK (BINDING TH thread-table))))))


(defthm framep-of-top-frame
  (implies (and (not (empty-call-stackp call-stack))
                (all-framep call-stack) ;drop when doing the all-framep-change
                (call-stackp call-stack))
           (framep (top-frame call-stack)))
  :hints (("Goal" :in-theory (enable top-frame empty-call-stackp call-stackp))))

(defthm framep-of-top-frame-of-binding-of-thread-table
  (IMPLIES (AND (call-stack-non-emptyp th s)
                (all-framep (BINDING TH (THREAD-TABLE S))) ;drop but strengthen CALL-STACKP
                (BOUND-IN-ALISTP TH (THREAD-TABLE S))
                (JVM-STATEP S)
                (THREAD-DESIGNATORP TH))
           (FRAMEP (TOP-FRAME (BINDING TH (THREAD-TABLE S)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable call-stack-non-emptyp JVM-STATEP ;THREAD-TABLEP
;EMPTY-CALL-STACKP ;TOP-FRAME
                              THREAD-TABLE))))

(defthm framep-of-thread-top-frame
  (implies (and (not (empty-call-stackp (binding th (thread-table s))))
                (all-framep (binding th (thread-table s))) ;drop
                (jvm-statep s)
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th))
           (framep (thread-top-frame th s)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable thread-top-frame))))
