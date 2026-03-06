; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(include-book "std/omaps/core" :dir :system)

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (include-book "total-order/total-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: move these definitions/theorems to std/omaps.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule omap-restrict-of-sfix
  (equal (omap::restrict (sfix keys) map)
         (omap::restrict keys map))
  :induct t
  :enable omap::restrict)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule equal-of-omap-assoc-and-cons
  (equal (equal (omap::assoc key1 omap)
                (cons key2 val))
         (and (omap::assoc key1 omap)
              (equal key1 key2)
              (equal (cdr (omap::assoc key1 omap)) val)))
  :induct t
  :enable omap::assoc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: These original definitions should probably be inline.

#!OMAP
(define emptyp$inline
  ((map mapp))
  (mbe :logic (emptyp map)
       :exec (null (the list map)))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable emptyp
                                           mapp))))

#!OMAP
(define tail$inline
  ((map mapp))
  (mbe :logic (tail map)
       :exec (cdr (the list map)))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tail
                                           mapp))))

#!OMAP
(define head$inline
  ((map mapp))
  :guard (not (emptyp map))
  (mbe :logic (head map)
       :exec (mv (caar map) (cdar map)))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable head
                                           mapp
                                           emptyp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-ruleset! omap-from-alist nil)

(defruled omapp-of-cons
  (implies (omap::mapp y)
           (equal (omap::mapp (cons x y))
                  (and (consp x)
                       (or (not y)
                           (<< (car x) (caar y))))))
  :enable omap::mapp)

(add-to-ruleset omap-from-alist '(omapp-of-cons))

(defruled omap-assoc-of-cons
  (implies (and (omap::mapp y)
                (consp x)
                (or (not y)
                    (<< (car x) (caar y))))
           (equal (omap::assoc a (cons x y))
                  (if (equal (car x) a)
                      x
                    (omap::assoc a y))))
  :induct t
  :enable (omap::assoc
           omap::head
           omap::tail
           omap-from-alist))

(add-to-ruleset omap-from-alist '(omap-assoc-of-cons))

;;;;;;;;;;;;;;;;;;;;

(defruled omapp-of-append
  (implies (omap::mapp x)
           (equal (omap::mapp (append x y))
                  (and (omap::mapp y)
                       (or (not x)
                           (not y)
                           (<< (caar (last x)) (caar y))))))
  :induct t
  :enable (append
           omap::mapp
           omap-from-alist))

(add-to-ruleset omap-from-alist '(omapp-of-append))

(defruled omap-assoc-of-append
  (implies (and (omap::mapp (append x y))
                (omap::mapp x))
           (equal (omap::assoc a (append x y))
                  (or (omap::assoc a x)
                      (omap::assoc a y))))
  :induct (omap::assoc a x)
  :enable (omap::assoc
           omap::mapp
           omap::emptyp
           omap::head
           omap::tail
           omap-from-alist))

(add-to-ruleset omap-from-alist '(omap-assoc-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap-assoc-becomes-assoc-equal
  (equal (omap::assoc key map)
         (assoc-equal key (omap::mfix map)))
  :induct t
  :enable (omap::assoc
           assoc-equal
           omap::mfix
           omap::mapp
           omap::emptyp
           omap::head
           omap::tail))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled size-becomes-len-when-omapp
  (implies (omap::mapp omap)
           (equal (omap::size omap)
                  (len omap)))
  :induct t
  :enable (omap::size
           omap::emptyp
           omap::tail
           omap::mapp))
