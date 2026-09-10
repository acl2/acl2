; Purely functional double-ended queues (deques), following Okasaki.
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Aakash Koneru

(in-package "DEQUE")

(include-book "kestrel/lists-light/reverse-list" :dir :system)
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))

(include-book "std/basic/defs" :dir :system)
(include-book "std/lists/list-fix" :dir :system)

(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;-------------------
; Documentation

(defxdoc+ deque
  :parents (data::data-lib)
  :short "Purely functional double-ended queues (deques)"
  :long
  (xdoc::topstring
    (xdoc::p
      "A <b>deque</b> (double-ended queue) is a finite sequence that supports
       inserting and removing elements at <i>both</i> ends, in constant
       amortized time O(1) under single-threaded usage. This is an implementation in the style of
       Okasaki's banker's deque: a deque is a front list consed together with
       a reversed rear list, plus the cached length of each side so the balance
       check never recomputes @('len').  Whenever one side grows more than
       three times the other, the deque is rebalanced by splitting the elements evenly.")
    (xdoc::p
      "@(tsee dequep) recognizes a well-formed deque and @(tsee deque->list)
       returns the sequence it denotes.  The operations are @(tsee empty-deque),
       @(tsee push-front), @(tsee push-back), @(tsee front), @(tsee back), @(tsee
       pop-front), @(tsee pop-back), @(tsee emptyp), @(tsee deque-size), and
       @(tsee list->deque).  @(tsee deque-equiv) equates deques that denote the
       same sequence, and every operation respects it.")))

(defxdoc dequep
  :parents (deque)
  :short "Recognize a well-formed deque (balanced, with correct cached lengths).")

(defxdoc deque->list
  :parents (deque)
  :short "The list of elements a deque denotes, from front to back.")

(defxdoc empty-deque
  :parents (deque)
  :short "The empty deque.")

(defxdoc push-front
  :parents (deque)
  :short "Add an element to the front of a deque.")

(defxdoc push-back
  :parents (deque)
  :short "Add an element to the back of a deque.")

(defxdoc front
  :parents (deque)
  :short "The front (leftmost) element of a deque."
  :long "<p>Returns @('nil') when the deque is empty (there is no front
         element).</p>")

(defxdoc back
  :parents (deque)
  :short "The back (rightmost) element of a deque."
  :long "<p>Returns @('nil') when the deque is empty (there is no back
         element).</p>")

(defxdoc pop-front
  :parents (deque)
  :short "Remove the front element of a deque."
  :long "<p>Returns the empty deque when the deque is already empty (there is
         no front element to remove).</p>")

(defxdoc pop-back
  :parents (deque)
  :short "Remove the back element of a deque."
  :long "<p>Returns the empty deque when the deque is already empty (there is
         no back element to remove).</p>")

(defxdoc emptyp
  :parents (deque)
  :short "Recognize the empty deque.")

(defxdoc deque-size
  :parents (deque)
  :short "The number of elements in a deque.")

(defxdoc list->deque
  :parents (deque)
  :short "Build a balanced deque holding the elements of a list, front to back.")

(defxdoc deque-equiv
  :parents (deque)
  :short "Equivalence relating deques that denote the same sequence of elements.")

;-------------------
;; Representation: a deque stores the front list, the (reversed) rear
;; list, and the lengths of both, so the balance check never recomputes LEN.
;; The sequence it denotes is (append front (reverse-list rear)).  Concretely a
;; deque is
;;   ((front . rear) . (flen . rlen)).


(defund weak-dequep (dq)
  (declare (xargs :guard t))
  (and (consp dq)
       (consp (car dq))
       (true-listp (caar dq))    ; front
       (true-listp (cdar dq))    ; rear
       (consp (cdr dq))
       (natp (cadr dq))          ; flen
       (natp (cddr dq))))        ; rlen

(defund weak-deque (f r flen rlen)
  (declare (xargs :guard (and (true-listp f) (true-listp r) (natp flen) (natp rlen))))
  (cons (cons (llist-fix f)
              (llist-fix r))
        (cons (lnfix flen)
              (lnfix rlen))))

(defthm weak-dequep-of-weak-deque
  (weak-dequep (weak-deque f r flen rlen))
  :hints (("Goal" :in-theory (enable weak-dequep weak-deque))))

(defund-inline weak-deque-fix (dq)
  (declare (xargs :guard (weak-dequep dq)))
  (mbe :logic (if (weak-dequep dq)
                  dq
                (weak-deque nil nil 0 0))
       :exec dq))

(defthm weak-dequep-of-weak-deque-fix
  (weak-dequep (weak-deque-fix dq))
  :hints (("Goal" :in-theory (enable weak-deque-fix))))

(defthm weak-deque-fix-when-weak-dequep
  (implies (weak-dequep dq)
           (equal (weak-deque-fix dq)
                  dq))
  :hints (("Goal" :in-theory (enable weak-deque-fix))))

(defund weak-deque->front (dq)
  (declare (xargs :guard (weak-dequep dq)
                  :guard-hints (("Goal" :in-theory (enable weak-dequep)))))
  (caar (weak-deque-fix dq)))

(defthm true-listp-of-weak-deque->front-type-prescription
  (true-listp (weak-deque->front dq))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable weak-deque->front
                                     weak-deque-fix
                                     weak-dequep))))

(defund weak-deque->rear (dq)
  (declare (xargs :guard (weak-dequep dq)
                  :guard-hints (("Goal" :in-theory (enable weak-dequep)))))
  (cdar (weak-deque-fix dq)))

(defund weak-deque->flen (dq)
  (declare (xargs :guard (weak-dequep dq)
                  :guard-hints (("Goal" :in-theory (enable weak-dequep)))))
  (cadr (weak-deque-fix dq)))

(defund weak-deque->rlen (dq)
  (declare (xargs :guard (weak-dequep dq)
                  :guard-hints (("Goal" :in-theory (enable weak-dequep)))))
  (cddr (weak-deque-fix dq)))

(defthm weak-deque->front-of-weak-deque
  (equal (weak-deque->front (weak-deque f r flen rlen))
         (true-list-fix f))
  :hints (("Goal" :in-theory (enable weak-deque
                                     weak-deque->front
                                     weak-deque-fix
                                     weak-dequep))))

(defthm weak-deque->rear-of-weak-deque
  (equal (weak-deque->rear (weak-deque f r flen rlen))
         (true-list-fix r))
  :hints (("Goal" :in-theory (enable weak-deque
                                     weak-deque->rear
                                     weak-deque-fix
                                     weak-dequep))))

(defthm weak-deque->flen-of-weak-deque
  (equal (weak-deque->flen (weak-deque f r flen rlen))
         (lnfix flen))
  :hints (("Goal" :in-theory (enable weak-deque
                                     weak-deque->flen
                                     weak-deque-fix
                                     weak-dequep))))

(defthm weak-deque->rlen-of-weak-deque
  (equal (weak-deque->rlen (weak-deque f r flen rlen))
         (lnfix rlen))
  :hints (("Goal" :in-theory (enable weak-deque
                                     weak-deque->rlen
                                     weak-deque-fix
                                     weak-dequep))))

(defthm natp-of-weak-deque->flen
  (natp (weak-deque->flen dq))
  :hints (("Goal" :in-theory (enable weak-deque->flen weak-deque-fix weak-dequep)))
  :rule-classes (:type-prescription))

(defthm natp-of-weak-deque->rlen
  (natp (weak-deque->rlen dq))
  :hints (("Goal" :in-theory (enable weak-deque->rlen weak-deque-fix weak-dequep)))
  :rule-classes (:type-prescription))

(defthm true-listp-of-weak-deque->rear
  (true-listp (weak-deque->rear dq))
  :hints (("Goal" :in-theory (enable weak-deque->rear weak-deque-fix weak-dequep)))
  :rule-classes (:type-prescription))

;-------------------
(defund deque->list (dq)
  (declare (xargs :guard (weak-dequep dq)))
  (append (weak-deque->front dq)
          (reverse-list (weak-deque->rear dq))))

(defthm deque->list-of-weak-deque
  (equal (deque->list (weak-deque f r flen rlen))
         (append f (reverse-list r)))
  :hints (("Goal" :in-theory (enable deque->list))))

;-------------------
; The balance invariant, now stated on the stored lengths.

; Neither side may exceed three times the length of the other, plus one.
(defund balancedp (flen rlen)
  (declare (xargs :guard (and (natp flen) (natp rlen))))
  (and (<= flen (+ (* 3 rlen) 1))
       (<= rlen (+ (* 3 flen) 1))))

; A deque satisfying the balance invariant, whose stored lengths are correct.
(defund dequep (dq)
  (declare (xargs :guard t))
  (and (weak-dequep dq)
       (equal (weak-deque->flen dq) (len (weak-deque->front dq)))
       (equal (weak-deque->rlen dq) (len (weak-deque->rear dq)))
       (balancedp (weak-deque->flen dq) (weak-deque->rlen dq))))

(defthm weak-dequep-when-dequep
  (implies (dequep dq)
           (weak-dequep dq))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable dequep))))

(defthm weak-deque->flen-when-dequep
  (implies (dequep dq)
           (equal (weak-deque->flen dq) (len (weak-deque->front dq))))
  :hints (("Goal" :in-theory (enable dequep))))

(defthm weak-deque->rlen-when-dequep
  (implies (dequep dq)
           (equal (weak-deque->rlen dq) (len (weak-deque->rear dq))))
  :hints (("Goal" :in-theory (enable dequep))))

(defund-inline deque-fix (dq)
  (declare (xargs :guard (dequep dq)))
  (mbe :logic (if (dequep dq)
                  dq
                (weak-deque nil nil 0 0))
       :exec dq))

(defthm dequep-of-deque-fix
  (dequep (deque-fix dq))
  :hints (("Goal" :in-theory (enable deque-fix dequep balancedp))))

(defthm deque-fix-when-dequep
  (implies (dequep dq)
           (equal (deque-fix dq)
                  dq))
  :hints (("Goal" :in-theory (enable deque-fix))))

;-------------------
; Rebalancing.  This is the O(n) path, so it may recompute LEN.

(local
  (defthm ceiling-of-2-<=-self-linear
    (implies (natp n)
             (<= (ceiling n 2) n))
    :rule-classes ((:linear :trigger-terms ((ceiling n 2))))))

(local
  (encapsulate ()
    (local (include-book "arithmetic-5/top" :dir :system))
    (defthmd halves-balanced
      (implies (natp n)
               (and (<= (ceiling n 2) (+ (* 3 (- n (ceiling n 2))) 1))
                    (<= (- n (ceiling n 2)) (+ (* 3 (ceiling n 2)) 1)))))))

; Recopy the elements into two evenly split lists, storing the new lengths.
(defund rebalance (f r flen rlen)
  (declare (xargs :guard (and (true-listp f) (true-listp r) (natp flen) (natp rlen))
                  :guard-hints (("Goal" :in-theory (enable natp)))))
  (let* ((all (append f (reverse-list r)))
         (n (+ flen rlen))
         (k (ceiling n 2)))
    (weak-deque (take k all)
                (reverse-list (nthcdr k all))
                k (- n k))))

(defthm deque->list-of-rebalance
  (implies (and (true-listp f) (true-listp r)
                (equal flen (len f)) (equal rlen (len r)))
           (equal (deque->list (rebalance f r flen rlen))
                  (append f (reverse-list r))))
  :hints (("Goal"
            :in-theory (e/d (rebalance deque->list
                                       acl2::append-of-take-and-nthcdr-2)
                            (acl2::take-of-append acl2::nthcdr-of-append-gen
                                            acl2::reverse-list-of-append)))))

(defthm dequep-of-rebalance
  (implies (and (equal flen (len f)) (equal rlen (len r)))
           (dequep (rebalance f r flen rlen)))
  :hints (("Goal" :in-theory (enable rebalance dequep balancedp)
                  :use (:instance halves-balanced
                                  (n (+ flen rlen))))))

; Build a deque from lists and their lengths, rebalancing if not balanced.
(defund mk-deque (f r flen rlen)
  (declare (xargs :guard (and (true-listp f) (true-listp r) (natp flen) (natp rlen))))
  (if (balancedp flen rlen)
      (weak-deque f r flen rlen)
    (rebalance f r flen rlen)))

(defthm deque->list-of-mk-deque
  (implies (and (true-listp f) (true-listp r)
                (equal flen (len f)) (equal rlen (len r)))
           (equal (deque->list (mk-deque f r flen rlen))
                  (append f (reverse-list r))))
  :hints (("Goal" :in-theory (enable mk-deque))))

(defthm dequep-of-mk-deque
  (implies (and (true-listp f) (true-listp r)
                (equal flen (len f)) (equal rlen (len r)))
           (dequep (mk-deque f r flen rlen)))
  :hints (("Goal" :in-theory (enable dequep mk-deque))))

;-------------------
; Operations

(defund empty-deque ()
  (declare (xargs :guard t))
  (weak-deque nil nil 0 0))

(defthm dequep-of-empty-deque
  (dequep (empty-deque))
  :hints (("Goal" :in-theory (enable dequep empty-deque balancedp))))

(defthm deque->list-of-empty-deque
  (equal (deque->list (empty-deque)) nil)
  :hints (("Goal" :in-theory (enable empty-deque))))

(in-theory (disable (:e empty-deque)))

(defund emptyp (dq)
  (declare (xargs :guard (dequep dq)
                  :guard-hints (("Goal" :in-theory (enable dequep)))))
  (let ((dq (deque-fix dq)))
    (and (atom (weak-deque->front dq))
         (atom (weak-deque->rear dq)))))

(defund deque-size (dq)
  (declare (xargs :guard (dequep dq)
                  :guard-hints (("Goal" :in-theory (enable dequep)))))
  (let ((dq (deque-fix dq)))
    (+ (weak-deque->flen dq)
       (weak-deque->rlen dq))))

(defthm deque-size-is-len-of-deque->list
  (equal (deque-size dq)
         (len (deque->list (deque-fix dq))))
  :hints (("Goal" :in-theory (enable deque-size deque->list))))

(defthm emptyp-iff-size-0
  (implies (dequep dq)
           (equal (emptyp dq)
                  (equal (deque-size dq) 0)))
  :hints (("Goal" :in-theory (e/d (emptyp deque-size dequep)
                                  (deque-size-is-len-of-deque->list)))))

(defthmd emptyp-iff-deque-fix-equal-empty-deque
  (equal (emptyp dq)
         (equal (deque-fix dq) (empty-deque)))
  :hints (("Goal" :in-theory (enable emptyp deque-fix empty-deque
                                     dequep
                                     weak-deque->front weak-deque->rear
                                     weak-deque->flen weak-deque->rlen
                                     weak-deque-fix weak-dequep
                                     ))))

(defund push-front (x dq)
  (declare (xargs :guard (dequep dq)
                  :guard-hints (("Goal" :in-theory (enable dequep)))))
  (let ((dq (deque-fix dq)))
    (mk-deque (cons x (weak-deque->front dq))
              (weak-deque->rear dq)
              (+ 1 (weak-deque->flen dq)) (weak-deque->rlen dq))))

(defthm dequep-of-push-front
  (dequep (push-front x dq))
  :hints (("Goal" :in-theory (enable push-front))))

(defund push-back (x dq)
  (declare (xargs :guard (dequep dq)
                  :guard-hints (("Goal" :in-theory (enable dequep)))))
  (let ((dq (deque-fix dq)))
    (mk-deque (weak-deque->front dq)
              (cons x (weak-deque->rear dq))
              (weak-deque->flen dq) (+ 1 (weak-deque->rlen dq)))))

(defthm dequep-of-push-back
  (dequep (push-back x dq))
  :hints (("Goal" :in-theory (enable push-back))))

; The leftmost element of the deque.
(defund front (dq)
  (declare (xargs :guard (dequep dq)
                  :guard-hints (("Goal" :in-theory (enable dequep)))))
  (let ((dq (deque-fix dq)))
    (if (consp (weak-deque->front dq))
        (car (weak-deque->front dq))
      ;else rlen = 1
      (car (weak-deque->rear dq)))))

(local
  (defthm car-of-reverse-list-when-len-<=-1
    (implies (<= (len x) 1)
             (equal (car (reverse-list x))
                    (car x)))
    :hints (("Goal" :in-theory (enable reverse-list)))))

(local
  (defthm car-of-last-when-len-<=-1
    (implies (<= (len x) 1)
             (equal (car (last x))
                    (car x)))
    :hints (("Goal" :in-theory (enable last)))))

(defthm front-is-car-of-deque->list
  (equal (front dq)
         (car (deque->list (deque-fix dq))))
  :hints (("Goal" :in-theory (e/d (front deque->list dequep balancedp deque-fix)
                                  (acl2::car-of-reverse-list)))))

; The rightmost element of the deque.
(defund back (dq)
  (declare (xargs :guard (dequep dq)
                  :guard-hints (("Goal" :in-theory (enable dequep)))))
  (let ((dq (deque-fix dq)))
    (if (consp (weak-deque->rear dq))
        (car (weak-deque->rear dq))
      ;else flen = 1
      (car (weak-deque->front dq)))))

(local
  (defthm car-of-reverse-list-is-car-of-last
    (equal (car (reverse-list l))
           (car (last l)))
    :hints (("Goal" :in-theory (enable reverse-list last)))))

(defthm back-is-last-of-deque->list
  (equal (back dq)
         (car (last (deque->list (deque-fix dq)))))
  :hints (("Goal" :in-theory (enable back deque->list dequep balancedp deque-fix))))

; Remove the front element.
(defund pop-front (dq)
  (declare (xargs :guard (dequep dq)
                  :guard-hints (("Goal" :in-theory (enable dequep)))))
  (let ((dq (deque-fix dq)))
    (if (consp (weak-deque->front dq))
        (mk-deque (cdr (weak-deque->front dq))
                  (weak-deque->rear dq)
                  (+ -1 (weak-deque->flen dq)) (weak-deque->rlen dq))
      (empty-deque))))

(defthm dequep-of-pop-front
  (dequep (pop-front dq))
  :hints (("Goal" :in-theory (enable pop-front))))

; Remove the back element.
(defund pop-back (dq)
  (declare (xargs :guard (dequep dq)
                  :guard-hints (("Goal" :in-theory (enable dequep)))))
  (let ((dq (deque-fix dq)))
    (if (consp (weak-deque->rear dq))
        (mk-deque (weak-deque->front dq)
                  (cdr (weak-deque->rear dq))
                  (weak-deque->flen dq) (+ -1 (weak-deque->rlen dq)))
      (empty-deque))))

(defthm dequep-of-pop-back
  (dequep (pop-back dq))
  :hints (("Goal" :in-theory (enable pop-back))))

; Build a (balanced) deque with the elements of a list.
(defund list->deque (l)
  (declare (xargs :guard (true-listp l)))
  (mk-deque (llist-fix l) nil (len l) 0))

(defthm dequep-of-list->deque
  (dequep (list->deque l))
  :hints (("Goal" :in-theory (enable list->deque))))

(defthm deque->list-of-list->deque
  (equal (deque->list (list->deque l))
         (true-list-fix l))
  :hints (("Goal" :in-theory (enable list->deque))))

;-------------------
; Deque equivalence.
;
; Two deques are "equal" when they contain the same sequence of elements, no
; matter how that sequence happens to be split between the front and rear
; lists, or what the stored lengths are.

(defund deque-equiv (dq1 dq2)
  (declare (xargs :guard (and (dequep dq1) (dequep dq2))))
  (equal (deque->list (deque-fix dq1))
         (deque->list (deque-fix dq2))))

(defequiv deque-equiv
  :hints (("Goal" :in-theory (enable deque-equiv))))

(defthm deque-equiv-of-list->deque-of-deque->list
  (implies (dequep dq)
           (deque-equiv (list->deque (deque->list dq)) dq))
  :hints (("Goal" :in-theory (enable deque-equiv))))

;-------------------
; Relationships between the operations.

(local
  (defthm rlen-<=-1-when-front-empty
    (implies (and (dequep dq)
                  (not (consp (weak-deque->front dq))))
             (<= (len (weak-deque->rear dq)) 1))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable dequep balancedp)))))

(local
  (defthm flen-<=-1-when-rear-empty
    (implies (and (dequep dq)
                  (not (consp (weak-deque->rear dq))))
             (<= (len (weak-deque->front dq)) 1))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable dequep balancedp)))))

(defthm deque->list-of-push-front
  (equal (deque->list (push-front x dq))
         (cons x (deque->list (deque-fix dq))))
  :hints (("Goal" :in-theory (enable push-front deque->list))))

(defthm deque->list-of-pop-front
  (equal (deque->list (pop-front dq))
         (cdr (deque->list (deque-fix dq))))
  :hints (("Goal" :in-theory (enable pop-front emptyp deque->list))))

(defthm deque-size-of-push-front
  (equal (deque-size (push-front x dq))
         (+ 1 (deque-size dq))))

(defthm deque-size-of-pop-front
  (implies (and (dequep dq)
                (not (emptyp dq)))
           (equal (deque-size (pop-front dq))
                  (+ -1 (deque-size dq)))))

(defthm front-of-push-front
  (equal (front (push-front x dq)) x))

(defthm not-emptyp-of-push-front
  (not (emptyp (push-front x dq))))

(defthm pop-front-of-push-front
  (deque-equiv (pop-front (push-front x dq)) dq)
  :hints (("Goal" :in-theory (enable deque-equiv))))

(defthmd emptyp-as-atom-of-deque->list
  (equal (emptyp dq)
         (atom (deque->list (deque-fix dq))))
  :hints (("Goal" :in-theory (enable emptyp deque->list))))

(defthm push-front-of-front-and-pop-front
  (implies (not (emptyp dq))
           (deque-equiv (push-front (front dq) (pop-front dq)) dq))
  :hints (("Goal" :in-theory (enable deque-equiv
                                     emptyp-as-atom-of-deque->list
                                     ))))


(defthm deque->list-of-push-back
  (equal (deque->list (push-back x dq))
         (append (deque->list (deque-fix dq)) (list x)))
  :hints (("Goal" :in-theory (enable push-back deque->list))))

(defthm deque->list-of-pop-back
  (equal (deque->list (pop-back dq))
         (butlast (deque->list (deque-fix dq)) 1))
  :hints (("Goal" :in-theory (enable pop-back emptyp deque->list))))

(defthm deque-size-of-push-back
  (equal (deque-size (push-back x dq))
         (+ 1 (deque-size dq))))

(defthm deque-size-of-pop-back
  (implies (and (dequep dq)
                (not (emptyp dq)))
           (equal (deque-size (pop-back dq))
                  (+ -1 (deque-size dq)))))

(defthm back-of-push-back
  (equal (back (push-back x dq)) x))

(defthm not-emptyp-of-push-back
  (not (emptyp (push-back x dq))))

(defthm pop-back-of-push-back
  (deque-equiv (pop-back (push-back x dq)) dq)
  :hints (("Goal" :in-theory (enable deque-equiv))))

(local
  (defthm append-of-take-of-len-1-and-last-elem
    (implies (and (true-listp x)
                  (consp x))
             (equal (append (take (+ -1 (len x)) x)
                            (list (car (last x))))
                    x))))

(local
  (defthm list-of-car-when-len-1
    (implies (and (true-listp x)
                  (equal (len x) 1))
             (equal (list (car x))
                    x))))

(defthm push-back-of-back-and-pop-back
  (implies (not (emptyp dq))
           (deque-equiv (push-back (back dq) (pop-back dq)) dq))
  :hints (("Goal" :in-theory (enable deque-equiv
                                     emptyp-as-atom-of-deque->list))))

;-------------------
; Congruence Rules.

(defthm push-front-when-deque-equiv-congruence
  (implies (deque-equiv dq0 dq1)
           (deque-equiv (push-front x dq0)
                        (push-front x dq1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable deque-equiv))))

(defthm push-back-when-deque-equiv-congruence
  (implies (deque-equiv dq0 dq1)
           (deque-equiv (push-back x dq0)
                        (push-back x dq1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable deque-equiv))))

(defthm pop-front-when-deque-equiv-congruence
  (implies (deque-equiv dq0 dq1)
           (deque-equiv (pop-front dq0)
                        (pop-front dq1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable deque-equiv))))

(defthm pop-back-when-deque-equiv-congruence
  (implies (deque-equiv dq0 dq1)
           (deque-equiv (pop-back dq0)
                        (pop-back dq1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable deque-equiv))))

(defthm front-when-deque-equiv-congruence
  (implies (deque-equiv dq0 dq1)
           (equal (front dq0)
                  (front dq1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable deque-equiv))))

(defthm back-when-deque-equiv-congruence
  (implies (deque-equiv dq0 dq1)
           (equal (back dq0)
                  (back dq1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable deque-equiv))))

(defthm deque-size-when-deque-equiv-congruence
  (implies (deque-equiv dq0 dq1)
           (equal (deque-size dq0)
                  (deque-size dq1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable deque-equiv))))

(defthm emptyp-when-deque-equiv-congruence
  (implies (deque-equiv dq0 dq1)
           (equal (emptyp dq0)
                  (emptyp dq1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable deque-equiv emptyp-as-atom-of-deque->list))))

;-------------------
; Linear rules on DEQUE-SIZE, useful for termination proofs that recur by
; popping a deque.

(defthm dequep-when-not-emptyp
  (implies (not (emptyp dq))
           (dequep dq))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable emptyp deque-fix))))

(defthm posp-of-deque-size-when-not-emptyp
  (implies (not (emptyp dq))
           (< 0 (deque-size dq)))
  :rule-classes :linear
  :hints (("Goal" :use emptyp-iff-size-0)))

(defthm deque-size-of-pop-front-linear
  (implies (not (emptyp dq))
           (< (deque-size (pop-front dq))
              (deque-size dq)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable deque-size-is-len-of-deque->list))))

(defthm deque-size-of-pop-back-linear
  (implies (not (emptyp dq))
           (< (deque-size (pop-back dq))
              (deque-size dq)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable deque-size-is-len-of-deque->list))))
