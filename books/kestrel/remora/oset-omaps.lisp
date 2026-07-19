; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "std/osets/top" :dir :system)
(include-book "std/omaps/top" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ oset-omaps
  :parents (library-extensions)
  :short "Theorems about finite sets (osets) and finite maps (omaps)
          used in the Remora library but more general."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule car-of-assoc
  (implies (omap::assoc key map)
           (equal (car (omap::assoc key map))
                  key))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :induct t
  :enable omap::assoc)

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

(defruled delete*-of-delete*-commute
  (equal (omap::delete* keys1 (omap::delete* keys2 map))
         (omap::delete* keys2 (omap::delete* keys1 map)))
  :expand ((omap::ext-equal (omap::delete* keys1 (omap::delete* keys2 map))
                            (omap::delete* keys2 (omap::delete* keys1 map)))
           (omap::ext-equal (omap::delete* keys2 (omap::delete* keys1 map))
                            (omap::delete* keys1 (omap::delete* keys2 map))))
  :use ((:instance omap::ext-equal-becomes-equal
                   (omap::x (omap::delete* keys1 (omap::delete* keys2 map)))
                   (omap::y (omap::delete* keys2 (omap::delete* keys1 map))))))

(defruled delete*-of-delete-commute
  (equal (omap::delete v (omap::delete* keys map))
         (omap::delete* keys (omap::delete v map)))
  :expand ((omap::ext-equal (omap::delete v (omap::delete* keys map))
                            (omap::delete* keys (omap::delete v map)))
           (omap::ext-equal (omap::delete* keys (omap::delete v map))
                            (omap::delete v (omap::delete* keys map))))
  :use ((:instance omap::ext-equal-becomes-equal
                   (omap::x (omap::delete v (omap::delete* keys map)))
                   (omap::y (omap::delete* keys (omap::delete v map))))))

(defruled delete*-commute-restricted
  (implies (syntaxp (and (symbolp bound)
                         (not (symbolp p))))
           (equal (omap::delete* p (omap::delete* bound map))
                  (omap::delete* bound (omap::delete* p map))))
  :use ((:instance delete*-of-delete*-commute (keys1 p) (keys2 bound))))

(defruled delete-commute-restricted
  (implies (syntaxp (symbolp bound))
           (equal (omap::delete v (omap::delete* bound map))
                  (omap::delete* bound (omap::delete v map))))
  :use ((:instance delete*-of-delete-commute (keys bound))))

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
