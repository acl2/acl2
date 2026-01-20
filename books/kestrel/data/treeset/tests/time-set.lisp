; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "std/osets/top" :dir :system)

(include-book "../delete")
(include-book "../in")
(include-book "../insert")
(include-book "../set")
(include-book "mk-set")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(program)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define do-set-ins
  ((list true-listp)
   (set setp))
  (if (endp list)
      nil
    (prog2$ (in (first list) set)
            (do-set-ins (rest list) set))))

(define do-oset-ins
  ((list true-listp)
   (set set::setp))
  (if (endp list)
      nil
    (prog2$ (set::in (first list) set)
            (do-oset-ins (rest list) set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define do-set-inserts
  ((list true-listp)
   (set setp))
  (if (endp list)
      nil
    (prog2$ (insert (first list) set)
            (do-set-inserts (rest list) set))))

(define do-oset-inserts
  ((list true-listp)
   (set set::setp))
  (if (endp list)
      nil
    (prog2$ (set::insert (first list) set)
            (do-oset-inserts (rest list) set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define do-set-deletes
  ((list true-listp)
   (set setp))
  (if (endp list)
      nil
    (prog2$ (delete (first list) set)
            (do-set-deletes (rest list) set))))

(define do-oset-deletes
  ((list true-listp)
   (set set::setp))
  (if (endp list)
      nil
    (prog2$ (set::delete (first list) set)
            (do-oset-deletes (rest list) set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define random-set-time-ins
  ((count-set natp)
   (count-ins natp)
   state)
  (b* (((mv set elements state)
        (mk-random-set count-set nil nil state))
       ((mv not-in state)
        (mk-random-obj-list-not-in count-ins set nil state))
       (in-count (acl2::min count-ins count-set))
       (in (take in-count elements))
       (list (append in not-in))
       (- (time$ (do-set-ins list set)
                 :msg "Time to check membership of ~x0 values in and ~x1 ~
                       (likely) not in the set of size ~x2: ~st seconds.~%"
                 :args (list in-count
                             count-ins
                             count-set))))
    (value '(value-triple :success))))

(define random-oset-time-ins
  ((count-set natp)
   (count-ins natp)
   state)
  (b* (((mv oset elements state)
        (mk-random-oset count-set nil nil state))
       (set (from-list elements))
       ((mv not-in state)
        (mk-random-obj-list-not-in count-ins set nil state))
       (in-count (acl2::min count-ins count-set))
       (in (take in-count elements))
       (list (append in not-in))
       (- (time$ (do-oset-ins list oset)
                 :msg "Time to check membership of ~x0 values in and ~x1 ~
                       (likely) not in the oset of size ~x2: ~st seconds.~%"
                 :args (list in-count
                             count-ins
                             count-set))))
    (value '(value-triple :success))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define random-set-time-inserts
  ((count-set natp)
   (count-inserts natp)
   state)
  (b* (((mv set elements state)
        (mk-random-set count-set nil nil state))
       ((mv not-in state)
        (mk-random-obj-list-not-in count-inserts set nil state))
       (in-count (acl2::min count-inserts count-set))
       (in (take in-count elements))
       (list (append in not-in))
       (- (time$ (do-set-inserts list set)
                 :msg "Time to insert of ~x0 values in and ~x1 (likely) not ~
                       in the set of size ~x2: ~st seconds.~%"
                 :args (list in-count
                             count-inserts
                             count-set))))
    (value '(value-triple :success))))

(define random-oset-time-inserts
  ((count-set natp)
   (count-inserts natp)
   state)
  (b* (((mv oset elements state)
        (mk-random-oset count-set nil nil state))
       (set (from-list elements))
       ((mv not-in state)
        (mk-random-obj-list-not-in count-inserts set nil state))
       (in-count (acl2::min count-inserts count-set))
       (in (take in-count elements))
       (list (append in not-in))
       (- (time$ (do-oset-inserts list oset)
                 :msg "Time to insert of ~x0 values in and ~x1 (likely) not ~
                       in the oset of size ~x2: ~st seconds.~%"
                 :args (list in-count
                             count-inserts
                             count-set))))
    (value '(value-triple :success))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define random-set-time-deletes
  ((count-set natp)
   (count-deletes natp)
   state)
  (b* (((mv set elements state)
        (mk-random-set count-set nil nil state))
       ((mv not-in state)
        (mk-random-obj-list-not-in count-deletes set nil state))
       (in-count (acl2::min count-deletes count-set))
       (in (take in-count elements))
       (list (append not-in in))
       (- (time$ (do-set-deletes list set)
                 :msg "Time to delete of ~x0 values in and ~x1 (likely) not ~
                       in the set of size ~x2: ~st seconds.~%"
                 :args (list in-count
                             count-deletes
                             count-set))))
    (value '(value-triple :success))))

(define random-oset-time-deletes
  ((count-set natp)
   (count-deletes natp)
   state)
  (b* (((mv oset elements state)
        (mk-random-oset count-set nil nil state))
       (set (from-list elements))
       ((mv not-in state)
        (mk-random-obj-list-not-in count-deletes set nil state))
       (in-count (acl2::min count-deletes count-set))
       (in (take in-count elements))
       (list (append not-in in))
       (- (time$ (do-oset-deletes list oset)
                 :msg "Time to delete of ~x0 values in and ~x1 (likely) not ~
                       in the oset of size ~x2: ~st seconds.~%"
                 :args (list in-count
                             count-deletes
                             count-set))))
    (value '(value-triple :success))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define consecutive-nat-set-time-ins
  ((count-set natp)
   (count-ins natp)
   state)
  (b* (((mv set elements)
        (mk-consecutive-nat-set count-set nil nil))
       ((mv not-in state)
        (mk-random-integer-list-not-in count-ins
                                       (1+ count-set)
                                       (* count-set 3)
                                       set
                                       nil
                                       state))
       (in-count (acl2::min count-ins count-set))
       (in (take in-count elements))
       (list (append in not-in))
       (- (time$ (do-set-ins list set)
                 :msg "Time to check membership of ~x0 values in and ~x1 not ~
                       in the consecutive nat set of size ~x2: ~st seconds.~%"
                 :args (list in-count
                             count-ins
                             count-set))))
    (value '(value-triple :success))))

(define consecutive-nat-oset-time-ins
  ((count-set natp)
   (count-ins natp)
   state)
  (b* (((mv oset elements)
        (mk-consecutive-nat-oset count-set nil nil))
       (set (from-list elements))
       ((mv not-in state)
        (mk-random-integer-list-not-in count-ins
                                       (1+ count-set)
                                       (* count-set 3)
                                       set
                                       nil
                                       state))
       (in-count (acl2::min count-ins count-set))
       (in (take in-count elements))
       (list (append in not-in))
       (- (time$ (do-oset-ins list oset)
                 :msg "Time to check membership of ~x0 values in and ~x1 not ~
                       in the consecutive nat oset of size ~x2: ~st seconds.~%"
                 :args (list in-count
                             count-ins
                             count-set))))
    (value '(value-triple :success))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define consecutive-nat-set-time-inserts
  ((count-set natp)
   (count-inserts natp)
   state)
  (b* (((mv set elements)
        (mk-consecutive-nat-set count-set nil nil))
       ((mv not-in state)
        (mk-random-integer-list-not-in count-inserts
                                       (1+ count-set)
                                       (* count-set 3)
                                       set
                                       nil
                                       state))
       (in-count (acl2::min count-inserts count-set))
       (in (take in-count elements))
       (list (append in not-in))
       (- (time$ (do-set-inserts list set)
                 :msg "Time to insert of ~x0 values in and ~x1 not in the ~
                       consecutive nat set of size ~x2: ~st seconds.~%"
                 :args (list in-count
                             count-inserts
                             count-set))))
    (value '(value-triple :success))))

(define consecutive-nat-oset-time-inserts
  ((count-set natp)
   (count-inserts natp)
   state)
  (b* (((mv oset elements)
        (mk-consecutive-nat-oset count-set nil nil))
       (set (from-list elements))
       ((mv not-in state)
        (mk-random-integer-list-not-in count-inserts
                                       (1+ count-set)
                                       (* count-set 3)
                                       set
                                       nil
                                       state))
       (in-count (acl2::min count-inserts count-set))
       (in (take in-count elements))
       (list (append in not-in))
       (- (time$ (do-oset-inserts list oset)
                 :msg "Time to insert of ~x0 values in and ~x1 not in the ~
                       consecutive nat oset of size ~x2: ~st seconds.~%"
                 :args (list in-count
                             count-inserts
                             count-set))))
    (value '(value-triple :success))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define consecutive-nat-set-time-deletes
  ((count-set natp)
   (count-deletes natp)
   state)
  (b* (((mv set elements)
        (mk-consecutive-nat-set count-set nil nil))
       ((mv not-in state)
        (mk-random-integer-list-not-in count-deletes
                                       (1+ count-set)
                                       (* count-set 3)
                                       set
                                       nil
                                       state))
       (in-count (acl2::min count-deletes count-set))
       (in (take in-count elements))
       (list (append not-in in))
       (- (time$ (do-set-deletes list set)
                 :msg "Time to delete of ~x0 values in and ~x1 not in the set ~
                       of size ~x2: ~st seconds.~%"
                 :args (list in-count
                             count-deletes
                             count-set))))
    (value '(value-triple :success))))

(define consecutive-nat-oset-time-deletes
  ((count-set natp)
   (count-deletes natp)
   state)
  (b* (((mv oset elements)
        (mk-consecutive-nat-oset count-set nil nil))
       (set (from-list elements))
       ((mv not-in state)
        (mk-random-integer-list-not-in count-deletes
                                       (1+ count-set)
                                       (* count-set 3)
                                       set
                                       nil
                                       state))
       (in-count (acl2::min count-deletes count-set))
       (in (take in-count elements))
       (list (append not-in in))
       (- (time$ (do-oset-deletes list oset)
                 :msg "Time to delete of ~x0 values in and ~x1 not in the ~
                       oset of size ~x2: ~st seconds.~%"
                 :args (list in-count
                             count-deletes
                             count-set))))
    (value '(value-triple :success))))
