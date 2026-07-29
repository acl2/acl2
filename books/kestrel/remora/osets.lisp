; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "std/osets/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ osets
  :parents (library-extensions)
  :short "Library extensions for osets."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Bridge lemmas between oset membership over SET::INSERT and the plain-list
; notions MEMBER-EQUAL, INTERSECTP-EQUAL, and SUBSETP-EQUAL: an insertion
; into an oset reads, at the list level, as consing on the inserted element.
; The bridge between SET::IN and MEMBER-EQUAL is SET::IN-TO-MEMBER.

(defruled member-equal-of-insert-when-setp
  (implies (set::setp x)
           (iff (member-equal a (set::insert b x))
                (or (equal a b) (member-equal a x))))
  :use ((:instance set::in-to-member (set::a a) (set::x (set::insert b x)))
        (:instance set::in-to-member (set::a a) (set::x x)))
  :enable (set::in-insert set::insert-produces-set))

(defruled intersectp-equal-of-insert-when-setp
  (implies (set::setp x)
           (iff (intersectp-equal l (set::insert b x))
                (or (member-equal b l)
                    (intersectp-equal l x))))
  :induct (intersectp-equal l x)
  :enable (intersectp-equal member-equal member-equal-of-insert-when-setp))

; The two SUBSETP-EQUAL facts go through the SET-EQUIV normal form of
; SET::INSERT; the book that provides it also installs a pick-a-point
; strategy for SUBSETP-EQUAL that can be disruptive in some client books,
; so it is included strictly locally here.

(encapsulate ()

  (local (include-book "std/osets/under-set-equiv" :dir :system))

  (defruled subsetp-equal-of-insert-right-when-setp
    (implies (set::setp x)
             (subsetp-equal x (set::insert a x)))
    :enable set::insert-under-set-equiv)

  (defruled subsetp-equal-of-insert-left-when-setp
    (implies (and (set::setp x)
                  (member-equal a l)
                  (subsetp-equal x l))
             (subsetp-equal (set::insert a x) l))
    :enable set::insert-under-set-equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled emptyp-intersect-of-union-left-1
  (implies (set::emptyp (set::intersect (set::union a b) c))
           (set::emptyp (set::intersect a c)))
  :use ((:instance set::in-head (set::x (set::intersect a c)))
        (:instance set::never-in-empty
                   (set::a (set::head (set::intersect a c)))
                   (set::x (set::intersect (set::union a b)
                                           c))))
  :disable set::in-head)

(defruled emptyp-intersect-of-union-left-2
  (implies (set::emptyp (set::intersect (set::union a b) c))
           (set::emptyp (set::intersect b c)))
  :use ((:instance set::in-head (set::x (set::intersect b c)))
        (:instance set::never-in-empty
                   (set::a (set::head (set::intersect b c)))
                   (set::x (set::intersect (set::union a b)
                                           c))))
  :disable set::in-head)

(defruled not-in-when-emptyp-intersect-of-insert
  (implies (set::emptyp (set::intersect (set::insert k s) b))
           (not (set::in k b)))
  :use ((:instance set::never-in-empty
                   (set::a k)
                   (set::x (set::intersect (set::insert k s)
                                           b)))))

(defruled emptyp-intersect3-binder-union
  (implies (set::emptyp
            (set::intersect (set::union other (set::difference fvb p))
                            (set::intersect bound keys)))
           (set::emptyp
            (set::intersect fvb
                            (set::intersect bound
                                            (set::difference keys p)))))
  :use ((:instance set::in-head
                   (set::x (set::intersect
                            fvb
                            (set::intersect bound
                                            (set::difference keys p)))))
        (:instance set::never-in-empty
                   (set::a (set::head
                       (set::intersect
                        fvb
                        (set::intersect bound
                                        (set::difference keys p)))))
                   (set::x (set::intersect (set::union other (set::difference fvb p))
                                           (set::intersect bound keys)))))
  :disable set::in-head)

(defruled emptyp-intersect3-binder-plain
  (implies (set::emptyp
            (set::intersect (set::difference fvb p)
                            (set::intersect bound keys)))
           (set::emptyp
            (set::intersect fvb
                            (set::intersect bound
                                            (set::difference keys p)))))
  :use ((:instance set::in-head
                   (set::x (set::intersect
                            fvb
                            (set::intersect bound
                                            (set::difference keys p)))))
        (:instance set::never-in-empty
                   (set::a (set::head
                       (set::intersect
                        fvb
                        (set::intersect bound
                                        (set::difference keys p)))))
                   (set::x (set::intersect (set::difference fvb p)
                                           (set::intersect bound keys)))))
  :disable set::in-head)

(defruled emptyp-intersect3-binder-delete
  (implies (set::emptyp
            (set::intersect (set::union other (set::delete v fvb))
                            (set::intersect bound keys)))
           (set::emptyp
            (set::delete v
                         (set::intersect fvb
                                         (set::intersect bound keys)))))
  :use ((:instance set::in-head
                   (set::x (set::delete
                            v
                            (set::intersect fvb
                                            (set::intersect bound keys)))))
        (:instance set::never-in-empty
                   (set::a (set::head
                       (set::delete
                        v
                        (set::intersect fvb
                                        (set::intersect bound keys)))))
                   (set::x (set::intersect (set::union other (set::delete v fvb))
                                           (set::intersect bound keys)))))
  :disable set::in-head)

(defruled emptyp-intersect-singleton
  (equal (set::emptyp (set::intersect (set::insert name nil) c))
         (not (set::in name c)))
  :enable (set::intersect))

(defruled emptyp-intersect-of-insert-union-1
  (implies (set::emptyp
            (set::intersect (set::insert k (set::union a b)) c))
           (set::emptyp (set::intersect a c)))
  :use ((:instance set::in-head (set::x (set::intersect a c)))
        (:instance set::never-in-empty
                   (set::a (set::head (set::intersect a c)))
                   (set::x (set::intersect (set::insert k (set::union a b))
                                           c))))
  :disable set::in-head)

(defruled emptyp-intersect-of-insert-union-2
  (implies (set::emptyp
            (set::intersect (set::insert k (set::union a b)) c))
           (set::emptyp (set::intersect b c)))
  :use ((:instance set::in-head (set::x (set::intersect b c)))
        (:instance set::never-in-empty
                   (set::a (set::head (set::intersect b c)))
                   (set::x (set::intersect (set::insert k (set::union a b))
                                           c))))
  :disable set::in-head)

(defruled emptyp-intersect-mono-right
  (implies (set::emptyp (set::intersect s bound))
           (set::emptyp (set::intersect s (set::intersect bound keys))))
  :use ((:instance set::in-head
                   (set::x (set::intersect s (set::intersect bound keys))))
        (:instance set::never-in-empty
                   (set::a (set::head
                       (set::intersect s (set::intersect bound keys))))
                   (set::x (set::intersect s
                                           bound))))
  :disable set::in-head)
