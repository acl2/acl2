; Misc utilities
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/sets/sets" :dir :system)
(include-book "coi/records/records" :dir :system) ;fixme why? g is called below
;(include-book "kestrel/utilities/mv-nth" :dir :system)
(include-book "kestrel/lists-light/memberp" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "kestrel/lists-light/first-non-member" :dir :system)
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(in-theory (disable mv-nth))

;move?
;see also lemma "dumb"
(defthm <-self
  (equal (< x x)
         nil))

;; ;fixme use a defmap?
;; (defund lookup-keys (keys record)
;;   (declare (xargs :guard (true-listp keys)))
;;   (if (endp keys)
;;       nil
;;     (cons (g (first keys) record)
;;           (lookup-keys (rest keys) record))))

;; (defthm memberp-of-g-and-lookup-keys
;;   (implies (memberp key keys)
;;            (memberp (g key map)
;;                           (lookup-keys keys map)))
;;   :hints (("Goal" :in-theory (enable lookup-keys))))

;move!

;dup
(defthm memberp-of-set2list
  (implies (set::setp set)
           (equal (memberp x (set::2list set))
                  (set::in x set))))

(defthm memberp-of-set2list
  (implies (set::setp set)
           (equal (memberp x (set::2list set))
                  (set::in x set))))

(defthm consp-of-2list-gen
  (equal (CONSP (SET::2LIST set))
         (not (set::empty set))))

(defthm 2list-of-singleton
  (equal (SET::2LIST (SET::INSERT ITEM NIL))
         (list item))
  :hints (("Goal" :expand ((SET::2LIST (LIST ITEM))
                           (SET::TAIL (LIST ITEM))
                           (SET::HEAD (LIST ITEM))
                           (SET::EMPTY (LIST ITEM))
                           (SET::SETP (LIST ITEM)))
           :in-theory (enable SET::INSERT SET::2LIST))))

(defthm delete-of-head
  (IMPLIES (NOT (SET::EMPTY X))
           (EQUAL (SET::DELETE (SET::HEAD X) X)
                  (SET::TAIL X))))

(defthm cdr-of-2-list
  (equal (cdr (set::2list x))
         (set::2list (set::tail x))))

(defthm car-of-2-list
  (implies (not (set::empty x))
           (equal (car (set::2list x))
                  (set::head x))))

(defthm in-of-head-and-tail-of-tail
  (not (set::in (set::head x)
                (set::tail (set::tail x)))))

(defthm head-of-insert-of-head-and-tail-of-tail
 (EQUAL (SET::HEAD (SET::INSERT (SET::HEAD X)
                                (SET::TAIL (SET::TAIL X))))
        (SET::HEAD X))
 :hints (("Goal" :in-theory (enable SET::TAIL SET::INSERT SET::HEAD SET::SFIX SET::EMPTY SET::SETP))))


;expensive?
(defthm head-of-insert-when-smallest
  (implies (not (equal (set::head (set::insert item set))
                       (set::head set)))
           (equal (set::head (set::insert item set))
                  item))
  :hints (("Goal" ;:expand ((set::delete item (cdr x)))
           :in-theory (enable set::tail set::insert set::head set::sfix set::empty set::setp))))

;expensive?
(defthm head-of-insert-when-not-smallest
  (implies (not (equal (set::head (set::insert item set))
                       item))
           (equal (set::head (set::insert item set))
                  (set::head set)))
  :hints (("Goal" ;:expand ((set::delete item (cdr x)))
           :in-theory (enable set::tail set::insert set::head set::sfix set::empty set::setp))))

(defthm in-of-car
  (equal (SET::IN (CAR SET) SET)
         (not (set::empty set)))
  :hints (("Goal" ;:expand ((set::delete item (cdr x)))
           :in-theory (enable set::tail set::insert set::head set::sfix set::empty set::setp set::in))))

(defthm tail-of-insert-when-smallest
  (IMPLIES (AND (EQUAL (SET::HEAD (SET::INSERT ITEM SET)) ;item is smaller than anything in the set
                       ITEM)
;               (NOT (SET::EMPTY SET))
                (NOT (SET::IN ITEM SET))
                (SET::SETP SET) ;drop?
                )
           (equal (SET::TAIL (SET::INSERT ITEM SET))
                  set))
  :hints (("Goal" ;:expand ((set::delete item (cdr x)))
           :in-theory (enable set::tail set::insert set::head set::sfix set::empty set::setp))))

(defthm tail-of-insert-when-not-smallest
  (implies (and (equal (set::head (set::insert item set)) ;item is not smaller than anything in the set
                       (set::head set))
                (not (set::in item set))
                (not (set::empty set)))
           (equal (set::tail (set::insert item set))
                  (set::insert item (set::tail set))))
  :otf-flg t
  :hints (("Goal" ;:expand ((set::delete item (cdr x)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable set::tail set::insert set::head set::sfix set::empty set::setp set::in)
           )))



;; ;this one does not require true-listp and allows us to do the defcong below:
;; (DEFUN my-STRING-LISTP (X)
;;   (DECLARE (XARGS :GUARD T))
;;   (COND ((ATOM X) t)
;;         (T (AND (STRINGP (CAR X))
;;                 (my-STRING-LISTP (CDR X))))))

;; (defthm string-listp-becomes-my-STRING-LISTP
;;   (equal (STRING-LISTP x)
;;          (and (true-listp x)
;;               (my-STRING-LISTP x))))

;breaks the set abstraction
(defthm subset-of-cdr
  (IMPLIES (AND (SET::SUBSET Y X)
                (SET::SETP y)
                )
           (SET::SUBSET (CDR Y) X))
  :hints (("Goal" :in-theory (e/d (set::subset SET::EMPTY SET::setp set::tail)
                                  (SET::PICK-A-POINT-SUBSET-STRATEGY)))))

(defthm <<-of-head-and-head-of-tail
  (implies (and (set::setp x)
                (not (set::empty x))
                (not (set::empty (set::tail x))))
           (<< (SET::HEAD X)
               (SET::HEAD (SET::TAIL X))))
  :hints (("Goal" :in-theory (enable set::tail set::insert set::head set::sfix set::empty set::setp set::subset))))

(defthm <<-of-head-when-not-equal-head
  (implies (and (set::in elem x)
                (set::setp x)
                (not (equal elem (set::head x))))
           (<< (set::head x) elem))
  :hints (("subgoal *1/3" :use (:instance <<-of-head-and-head-of-tail))
          ("Goal" :expand (SET::SETP X)
           :in-theory (enable set::in ;set::head
                              set::setp set::empty))))


(defthm setp-of-singleton
  (SET::setp (LIST ITEM))
  :hints (("Goal" :in-theory (enable SET::setp))))

(defthm empty-of-singleton
  (equal (SET::EMPTY (LIST ITEM))
         nil)
  :hints (("Goal" :in-theory (enable SET::EMPTY))))

(defthm head-of-cons
  (equal (set::head (cons item lst))
         (if (set::setp (cons item lst))
             item
           nil))
  :hints (("Goal" :in-theory (enable SET::SETP SET::HEAD SET::SFIX SET::EMPTY))))

(defthm head-of-insert-of-head-when-subset
  (implies (set::subset y x)
           (equal (set::head (set::insert (set::head x) y))
                  (set::head x)))
  :hints (("Goal" :in-theory (enable set::tail set::insert ;set::head
                                     set::sfix set::empty set::setp set::subset))))

(defthm subset-of-delete-when-subset
  (implies (set::subset set1 set2)
           (SET::SUBSET (SET::DELETE KEY set1) SET2)))

;move
(in-theory (disable acl2::nonnegative-integer-quotient))

;defforall could do this - maybe that's overkill because first-non-member is kind of an unusual function...
(defthm stringp-of-first-non-member
  (implies (and ;(string-listp lst2)
                (string-listp lst1)
                (not (acl2::subsetp-equal lst1 lst2))
                )
           (stringp (first-non-member lst1 lst2)))
  :hints (("Goal" :in-theory (enable first-non-member))))

(defthmd first-non-member-when-memberp
  (implies (memberp (car items) lst)
           (equal (first-non-member items lst)
                  (first-non-member (cdr items) lst))))

(defthm first-non-member-when-not-memberp
  (implies (not (memberp (car items) lst))
           (equal (first-non-member items lst)
                  (car items))))

;; ;improve proof?
;; (defthm SUBSET-EQ-of-REVERSE-LIST
;;   (equal (ACL2::SUBSET-EQ (ACL2::REVERSE-LIST x) y)
;;          (ACL2::SUBSET-EQ x y))
;;   :hints (("Goal" :in-theory (enable ACL2::REVERSE-LIST ACL2::SUBSET-EQ))))

(defthm string-listp-of-reverse-list
  (implies (true-listp x)
           (equal (string-listp (ACL2::REVERSE-LIST x))
                  (string-listp x)))
  :hints (("Goal" :in-theory (enable ACL2::REVERSE-LIST STRING-LISTP))))
