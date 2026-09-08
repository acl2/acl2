; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "std/omaps/top" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ omaps
  :parents (library-extensions)
  :short "Library extensions for omaps."
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
