; An efficient implementation of sets using fast-alists
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(include-book "kestrel/typed-lists-light/all-consp" :dir :system)

(local (in-theory (disable hons-assoc-equal hons-acons fast-alist-fork fast-alist-clean)))

(local
  (defthm not-consp-of-cdr-of-last
    (not (consp (cdr (last x))))))

(defthm hons-assoc-equal-when-not-consp
  (implies (not (consp alist))
           (equal (hons-assoc-equal key alist)
                  nil))
  :hints (("Goal" :in-theory (enable hons-assoc-equal))))

(defthm hons-assoc-equal-of-fast-alist-fork
  (equal (hons-assoc-equal val (fast-alist-fork alist ans))
       (if (hons-assoc-equal val ans)
           (hons-assoc-equal val ans)
         (hons-assoc-equal val alist)))
  :hints (("Goal" :in-theory (enable fast-alist-fork HONS-ASSOC-EQUAL ))))

(defthm hons-assoc-equal-of-fast-alist-clean
  (equal (hons-assoc-equal val (fast-alist-clean alist))
         (hons-assoc-equal val alist))
  :hints (("Goal" :in-theory (enable fast-alist-clean ))))

;; The param names here are chosen to match std
(defthm hons-assoc-equal-of-hons-acons
  (equal (hons-assoc-equal key (hons-acons key2 val map))
         (if (equal key key2)
             (cons key val)
           (hons-assoc-equal key map)))
  :hints (("Goal" :in-theory (enable hons-assoc-equal hons-acons))))

(defthm true-listp-of-hons-acons
  (equal (true-listp (hons-acons key val alist))
         (true-listp alist))
  :hints (("Goal" :in-theory (enable hons-acons))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; like strip-cars but tolerates non-conses
;; For execution only.
(defund fast-alist-keys-exec (alist acc)
  (declare (xargs :guard (true-listp acc)))
  (if (atom alist)
      (reverse acc)
    (let ((entry (first alist)))
      (fast-alist-keys-exec (rest alist) (if (consp entry)
                                             (cons (car entry) acc)
                                           ;; ignore non-conses in the alist:
                                           acc)))))

;; Easier to reason about (no accumulator)
(defund fast-alist-keys-simple (alist)
  (if (atom alist)
      nil
    (let ((entry (first alist)))
      (if (consp entry)
          (cons (car entry) (fast-alist-keys-simple (rest alist)))
        ;; ignore non-conses in the alist:
        (fast-alist-keys-simple (rest alist))))))

(defthmd member-equal-of-fast-alist-keys-simple-iff-hons-assoc-equal
  (iff (member-equal key (fast-alist-keys-simple alist))
       (hons-assoc-equal key alist))
  :hints (("Goal" :in-theory (enable hons-assoc-equal member-equal fast-alist-keys-simple))))

(defthm fast-alist-keys-simple-when-not-consp
  (implies (not (consp alist))
           (equal (fast-alist-keys-simple alist)
                  nil))
  :hints (("Goal" :in-theory (enable fast-alist-keys-simple))))

(defthmd fast-alist-keys-exec-becomes-fast-alist-keys-simple
  (implies (true-listp acc)
           (equal (fast-alist-keys-exec alist acc)
                  (append (reverse acc) (fast-alist-keys-simple alist))))
  :hints (("Goal" :in-theory (enable fast-alist-keys-simple
                                     fast-alist-keys-exec))))

;; (defthm no-duplicatesp-equal-of-fast-alist-keys-simple
;;   (implies (and (no-duplicatesp-equal (fast-alist-keys-simple set))
;;                 (not (intersection-equal acc (fast-alist-keys-simple set)))
;;                 (no-duplicatesp-equal acc)
;;                 (true-listp acc)
;;                 (fast-alist-setp set))
;;            (no-duplicatesp-equal (fast-alist-keys-simple set)))
;;   :hints (("Goal" :in-theory (enable fast-alist-keys-simple))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; like strip-cars but tolerates non-conses
(defund fast-alist-keys (alist)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fast-alist-keys-exec-becomes-fast-alist-keys-simple)))))
  (mbe :logic (fast-alist-keys-simple alist)
       :exec (fast-alist-keys-exec alist nil)))

(defthm true-listp-of-fast-alist-keys-type
  (true-listp (fast-alist-keys alist))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fast-alist-keys))))

(defthm fast-alist-keys-when-not-consp
  (implies (not (consp alist))
           (equal (fast-alist-keys alist)
                  nil))
  :hints (("Goal" :in-theory (enable fast-alist-keys))))

(defthm no-duplicatesp-equal-of-fast-alist-keys-of-cdr
  (implies (no-duplicatesp-equal (fast-alist-keys set))
           (no-duplicatesp-equal (fast-alist-keys (cdr set))))
  :hints (("Goal" :in-theory (enable fast-alist-keys fast-alist-keys-exec fast-alist-keys-exec-becomes-fast-alist-keys-simple
                                     fast-alist-keys-simple))))

(defthm no-duplicatesp-equal-of-fast-alist-keys-of-fast-alist-fork
  (implies (no-duplicatesp-equal (fast-alist-keys ans))
           (no-duplicatesp-equal (fast-alist-keys (fast-alist-fork alist ans))))
  :hints (("Goal" :in-theory (enable fast-alist-fork fast-alist-keys
                                     member-equal-of-fast-alist-keys-simple-iff-hons-assoc-equal
                                     fast-alist-keys-exec-becomes-fast-alist-keys-simple
                                     fast-alist-keys-simple))))

(defthm no-duplicatesp-equal-of-fast-alist-keys-of-fast-alist-clean
  (no-duplicatesp-equal (fast-alist-keys (fast-alist-clean alist)))
  :hints (("Goal" :in-theory (enable fast-alist-clean))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A set represented as a fast-alist. Elements in the set are bound to t.
;; Elements not in the set are either bound to nil or not bound to anything.
(defund fast-alist-setp (set)
  (declare (xargs :guard t ))
  (if (atom set)
      (or ;; (null set)    ; neither a size nor a name
          (natp set)    ; size hint
          ;; (symbolp set) ; name
          )
    (let ((entry (first set)))
      (and (consp entry)
           (booleanp (cdr entry)) ; whether the element is present in the set
           (fast-alist-setp (rest set))))))

;; Don't break the abstraction
(in-theory (disable (:e fast-alist-setp)))

(defthm fast-alist-setp-of-cdr
  (implies (and (fast-alist-setp set)
                (consp set))
           (fast-alist-setp (cdr set)))
  :hints (("Goal" :in-theory (enable fast-alist-setp))))

;; Note that cdr of last is the final-cdr.
(defthm fast-alist-setp-of-cdr-of-last
  (implies (and (fast-alist-setp set)
                (consp set))
           (fast-alist-setp (cdr (last set))))
  :hints (("Goal" :in-theory (enable fast-alist-setp))))

(defthm fast-alist-setp-of-cons
  (equal (fast-alist-setp (cons entry set))
         (and (fast-alist-setp set)
              (consp entry)
              (booleanp (cdr entry))))
  :hints (("Goal" :in-theory (enable fast-alist-setp))))

(defthm fast-alist-setp-of-fast-alist-fork
  (implies (and (fast-alist-setp alist)
                (fast-alist-setp ans))
           (fast-alist-setp (fast-alist-fork alist ans)))
  :hints (("Goal" :in-theory (enable fast-alist-fork))))

(defthm fast-alist-setp-of-fast-alist-clean
  (implies (fast-alist-setp alist)
           (fast-alist-setp (fast-alist-clean alist)))
  :hints (("Goal" :in-theory (enable fast-alist-clean))))

(defthm all-consp-when-FAST-ALIST-SETP
  (implies (FAST-ALIST-SETP set)
           (all-consp set))
  :hints (("Goal" :in-theory (enable FAST-ALIST-SETP all-consp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks whether VAL is in the set (whether it is bound to T in the alist).
(defund fast-alist-set-memberp (val set)
  (declare (xargs :guard (fast-alist-setp set)))
  (let ((pair (hons-get val set)))
    (and pair (eq t (cdr pair)))))

(defthm not-fast-alist-set-memberp-when-not-consp
  (implies (not (consp set))
           (not (fast-alist-set-memberp val set)))
  :hints (("Goal" :in-theory (enable fast-alist-set-memberp hons-assoc-equal))))

(defthm fast-alist-set-memberp-of-fast-alist-fork-iff
  (implies (not (hons-assoc-equal val ans))
           (iff (fast-alist-set-memberp val (fast-alist-fork alist ans))
                (fast-alist-set-memberp val alist)))
  :hints (("Goal" :in-theory (enable fast-alist-set-memberp))))

(defthm fast-alist-set-memberp-of-fast-alist-clean-iff
  (iff (fast-alist-set-memberp val (fast-alist-clean set))
       (fast-alist-set-memberp val set))
  :hints (("Goal" :in-theory (enable fast-alist-clean))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund empty-fast-alist-set (size)
  (declare (xargs :guard (natp size))) ; ignored if < 60?
  (nfix size) ; a fast-alist that is an atom is just a size hint
  )

;; Don't break the abstraction
(in-theory (disable (:e empty-fast-alist-set)
                    (:t empty-fast-alist-set)))

(defthm fast-alist-setp-of-empty-fast-alist-set
  (fast-alist-setp (empty-fast-alist-set size))
  :hints (("Goal" :in-theory (enable empty-fast-alist-set fast-alist-setp))))

;; Nothing is in the empty set
(defthm not-fast-alist-set-memberp-of-empty-fast-alist-set
  (not (fast-alist-set-memberp val (empty-fast-alist-set size)))
  :hints (("Goal" :in-theory (enable fast-alist-set-memberp
                                     empty-fast-alist-set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Adds VAL to the SET (no change if it is already a member).
(defund add-to-fast-alist-set (val set)
  (declare (xargs :guard (fast-alist-setp set)))
  (if (fast-alist-set-memberp val set)
      set
    (hons-acons val t set)))

(defthm fast-alist-setp-of-add-to-fast-alist-set
  (implies (fast-alist-setp set)
           (fast-alist-setp (add-to-fast-alist-set val set)))
  :hints (("Goal" :in-theory (enable add-to-fast-alist-set hons-acons))))

;; If we add an element, is becomes a member.
(defthm fast-alist-set-memberp-of-add-to-fast-alist-set-same
  (fast-alist-set-memberp val (add-to-fast-alist-set val set))
  :hints (("Goal" :in-theory (enable fast-alist-set-memberp add-to-fast-alist-set))))

;; Adding a different element has no effect.
(defthm fast-alist-set-memberp-of-add-to-fast-alist-set-diff
  (implies (not (equal val1 val2))
           (equal (fast-alist-set-memberp val1 (add-to-fast-alist-set val2 set))
                  (fast-alist-set-memberp val1 set)))
  :hints (("Goal" :in-theory (enable fast-alist-set-memberp add-to-fast-alist-set))))

(defthm fast-alist-set-memberp-of-add-to-fast-alist-set-both
  (equal (fast-alist-set-memberp val1 (add-to-fast-alist-set val2 set))
         (if (equal val1 val2)
             t
           (fast-alist-set-memberp val1 set))))

(defthm add-to-fast-alist-set-of-add-to-fast-alist-set
  (equal (fast-alist-set-memberp val3 (add-to-fast-alist-set val1 (add-to-fast-alist-set val2 set)))
         (fast-alist-set-memberp val3 (add-to-fast-alist-set val2 (add-to-fast-alist-set val1 set))))
  :hints (("Goal" :in-theory (enable add-to-fast-alist-set fast-alist-set-memberp hons-assoc-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Removes VAL from the set (by mapping it to nil).  No change if VAL is not a member.
;; todo: add a way to remove the pairs that map things to nil?
(defund remove-from-fast-alist-set (val set)
  (declare (xargs :guard (fast-alist-setp set)))
  (if (fast-alist-set-memberp val set)
      (hons-acons val nil set)
    set))

;; If we remove an element, it is no longer a member.
(defthm fast-alist-set-memberp-of-remove-from-fast-alist-set-same
  (not (fast-alist-set-memberp val (remove-from-fast-alist-set val set)))
  :hints (("Goal" :in-theory (enable fast-alist-set-memberp
                                     remove-from-fast-alist-set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helper function.
;; Maps each element of LIST to T in FAST-ALIST.
(defun list-to-fast-alist-set-aux (list set)
  (declare (xargs :guard (and (true-listp list)
                              (fast-alist-setp set))))
  (if (endp list)
      set
    (list-to-fast-alist-set-aux (rest list) (add-to-fast-alist-set (first list) set))))

(defthm equal-of-fast-alist-set-memberp-of-list-to-fast-alist-set-aux-helper
  (implies (equal (fast-alist-set-memberp val set1)
                  (fast-alist-set-memberp val set2))
           (equal (equal (fast-alist-set-memberp val (list-to-fast-alist-set-aux list set1))
                         (fast-alist-set-memberp val (list-to-fast-alist-set-aux list set2)))
                  t)))

(defthm fast-alist-set-memberp-of-list-to-fast-alist-set-aux
  (iff (fast-alist-set-memberp val (list-to-fast-alist-set-aux list set))
       (or (fast-alist-set-memberp val set)
           (member-equal val list))))

;; Converts LIST to a fast-alist-set.
(defun list-to-fast-alist-set (list)
  (let* ((len (len list))
         (fast-alist-set (empty-fast-alist-set (* 2 len))))
    (list-to-fast-alist-set-aux list fast-alist-set)))

;; A value is in the set iff it was in the list.
(defthm fast-alist-set-memberp-of-list-to-fast-alist-set
  (iff (fast-alist-set-memberp val (list-to-fast-alist-set list))
       (member-equal val list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper function.
(defund fast-alist-set-to-list-aux (set acc)
  (declare (xargs :guard (and (fast-alist-setp set)
                              (no-duplicatesp-equal (fast-alist-keys set)))))
  (if (atom set)
      acc ; could reverse here...
    (let ((entry (first set)))
      (if (cdr entry)
          ;; item is marked as present:
          (fast-alist-set-to-list-aux (rest set) (cons (car entry) acc))
        ;; item is marked as not present:
        (fast-alist-set-to-list-aux (rest set) acc)))))

(defthm no-duplicatesp-equal-of-fast-alist-set-to-list-aux
  (implies (and (no-duplicatesp-equal (fast-alist-keys alist))
                (no-duplicatesp-equal acc)
                (not (intersection-equal acc (fast-alist-keys alist))))
           (no-duplicatesp-equal (fast-alist-set-to-list-aux alist acc)))
  :hints (("Goal" :in-theory (enable fast-alist-set-to-list-aux fast-alist-keys
                                     fast-alist-keys-exec-becomes-fast-alist-keys-simple
                                     fast-alist-keys-simple))))

(defthm member-equal-of-fast-alist-set-to-list-aux
  (implies (and (fast-alist-setp set)
                (no-duplicatesp-equal (fast-alist-keys set)))
           (iff (member-equal val (fast-alist-set-to-list-aux set acc))
                (or (member-equal val acc)
                    (fast-alist-set-memberp val set))))
  :hints (("Goal" :in-theory (enable fast-alist-set-to-list-aux
                                     fast-alist-set-memberp
                                     hons-assoc-equal
                                     fast-alist-setp
                                     fast-alist-keys
                                     fast-alist-keys-simple
                                     member-equal-of-fast-alist-keys-simple-iff-hons-assoc-equal))))

;; The order of the result is arbitrary, so consider sorting it.
;; Warning: This steals the hash table from set?  TODO: So should we return the cleaned alist?
(defund fast-alist-set-to-list (set)
  (declare (xargs :guard (fast-alist-setp set)))
  (fast-alist-free-on-exit set (fast-alist-set-to-list-aux (fast-alist-clean set) nil)))

(defthm no-duplicatesp-equal-of-fast-alist-set-to-list
  (no-duplicatesp-equal (fast-alist-set-to-list set))
  :hints (("Goal" :in-theory (enable fast-alist-set-to-list
                                     fast-alist-keys-exec-becomes-fast-alist-keys-simple))))

;; A value is in the list iff it was in the set.
(defthm member-equal-of-fast-alist-set-to-list-iff
  (implies (fast-alist-setp set) ; drop?
           (iff (member-equal val (fast-alist-set-to-list set))
                (fast-alist-set-memberp val set)))
  :hints (("Goal" :in-theory (enable fast-alist-set-to-list))))

(local
  (defthm not-consp-of-cdr-of-last-type
    (not (consp (CDR (LAST alist))))
    :rule-classes :type-prescription))

;(include-book "kestrel/alists-light/clear-key" :dir :system)

(defun clear-key2 (key alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      alist ; preserve fast alist name or size
    (if (equal key (caar alist))
        (clear-key2 key (cdr alist))
      (cons (car alist)
            (clear-key2 key (cdr alist))))))

(defund remove-bad-and-shadowed-pairs (alist)
  (declare (xargs :measure (len alist)))
  (if (atom alist)
      alist
    (let ((entry (first alist)))
      (if (not (consp entry))
          (remove-bad-and-shadowed-pairs (rest alist))
        (cons entry (remove-bad-and-shadowed-pairs (clear-key2 (car entry) (rest alist))))))))

;; (defthm true-list-of-remove-bad-and-shadowed-pairs-type
;;   (implies (true-listp alist)
;;            (true-listp (remove-bad-and-shadowed-pairs alist)))
;;   :rule-classes :type-prescription)

(defund clear-keys-simple (keys alist)
  (if (endp alist)
      alist
    (let ((entry (first alist)))
      (if (not (consp entry))
          (clear-keys-simple keys (rest alist)) ; removes non-conses
        (if (member-equal (car entry) keys)
            (clear-keys-simple keys (rest alist))
          (cons entry (clear-keys-simple keys (rest alist))))))))

(defthm true-list-of-clear-keys-simple-type
  (implies (true-listp alist)
           (true-listp (clear-keys-simple keys alist)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable clear-keys-simple))))

(defthm clear-keys-simple-of-nil
  (implies (alistp alist)
           (equal (clear-keys-simple nil alist)
                  alist))
  :hints (("Goal" :in-theory (enable clear-keys-simple))))

(defthm not-member-equal-of-strip-cars-of-clear-keys-simple
  (implies (not (member-equal key (strip-cars alist)))
           (not (member-equal key (strip-cars (clear-keys-simple keys alist)))))
  :hints (("Goal" :in-theory (enable clear-keys-simple))))

(defthm clear-keys-simple-of-cons
  (implies t ;(true-listp alist)
           (equal (clear-keys-simple (cons key keys) alist)
                  (clear-key2 key (clear-keys-simple keys alist))))
  :hints (("Goal" :in-theory (enable clear-keys-simple clear-key2))))

(defthm clear-keys-simple-of-nil-arg1
  (implies (all-consp set)
           (equal (clear-keys-simple nil set)
                  set))
  :hints (("Goal" :in-theory (enable clear-keys-simple))))

;move
(defthmd hons-assoc-equal-iff
  (implies (alistp alist)
           (iff (HONS-ASSOC-EQUAL key alist)
                (member-equal key (strip-cars alist))))
  :hints (("Goal" :in-theory (enable HONS-ASSOC-EQUAL member-equal strip-cars))))

(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

;better?
(local
  (DEFTHM HONS-ASSOC-EQUAL-IFF-2
    (IMPLIES (all-consp alist)
             (IFF (HONS-ASSOC-EQUAL KEY ALIST)
                  (MEMBER-EQUAL KEY (STRIP-CARS ALIST))))
    :HINTS
    (("Goal" :IN-THEORY (ENABLE HONS-ASSOC-EQUAL
                                MEMBER-EQUAL STRIP-CARS)))))

(defthmd fast-alist-fork-redef
  (implies (and ;(true-listp alist)
                ;(alistp ans)
                (all-consp ans)
                )
           (equal (fast-alist-fork alist ans)
                  (append (reverse (remove-bad-and-shadowed-pairs (clear-keys-simple (strip-cars ans) alist)))
                          ans)))
  :hints (("Goal" :expand (REMOVE-BAD-AND-SHADOWED-PAIRS (CONS (CAR ALIST)
                                                               (CLEAR-KEYS-SIMPLE (STRIP-CARS ANS)
                                                                                  (CDR ALIST))))
           :in-theory (enable fast-alist-fork REMOVE-BAD-AND-SHADOWED-PAIRS
                              hons-assoc-equal-iff
                              clear-keys-simple))))

;; (thm
;;   (implies (and (not (HONS-ASSOC-EQUAL KEY ANS))
;;                 (not (HONS-ASSOC-EQUAL KEY alist))
;;                 (true-listp alist)
;;                 (alistp alist) ; todo
;;                 (alistp ans))
;;            (equal (fast-alist-fork (hons-acons key val alist) ans)
;;                   (hons-acons key val (fast-alist-fork alist ans))))
;;   :hints (("Goal" :in-theory (e/d (fast-alist-fork-redef) (STRIP-CARS CLEAR-KEYS-SIMPLE alistp)))))

(defthm cdr-of-last-of-hons-acons
  (Implies (true-listp alist) ; gen?
           (equal (cdr (last (hons-acons key val alist)))
                  (cdr (last alist))))
  :hints (("Goal" :in-theory (enable hons-acons))))

(local (in-theory (disable last)))

(defthm all-consp-of-hons-acons
  (implies (all-consp l)
           (all-consp (hons-acons key val l)))
  :hints (("Goal" :in-theory (enable hons-acons))))

;; (thm
;;   (implies (fast-alist-setp set)
;;            (equal (fast-alist-set-to-list (add-to-fast-alist-set a set))
;;                   (if (fast-alist-set-memberp a set)
;;                       set
;;                     (cons a (fast-alist-set-to-list set)))))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (enable fast-alist-set-to-list
;;                                      fast-alist-set-to-list-aux
;;                                      add-to-fast-alist-set
;;                                      fast-alist-set-memberp
;;                                      FAST-ALIST-CLEAN
;;                                      fast-alist-fork-redef
;;                                      ;HONS-ASSOC-EQUAL
;;                                      ))))
