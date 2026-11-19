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
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(include-book "std/omaps/core" :dir :system)

(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/butlast" :dir :system))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled in-of-omap-keys-when-omap-rlookup
  (implies (in key (omap::rlookup val omap))
           (in key (omap::keys omap)))
  :induct t
  :enable omap::rlookup)

(defrule in-of-omap-keys-when-omap-rlookup-forward-chaining
  (implies (in key (omap::rlookup val omap))
           (in key (omap::keys omap)))
  :rule-classes :forward-chaining
  :by in-of-omap-keys-when-omap-rlookup)

(defrule subset-of-omap-rlookup-and-omap-keys
  (subset (omap::rlookup val omap)
          (omap::keys omap))
  :enable set::expensive-rules)

(defrule in-of-omap-rlookup
  (equal (in key (omap::rlookup val omap))
         (and (omap::assoc key omap)
              (equal (cdr (omap::assoc key omap)) val)))
  :induct t
  :hints ('(:use (:instance in-of-omap-keys-when-omap-rlookup
                            (key (mv-nth 0 (omap::head omap)))
                            (omap (omap::tail omap)))))
  :enable (omap::rlookup
           omap::assoc)
  :disable in-of-omap-keys-when-omap-rlookup-forward-chaining)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled in-of-omap-values-becomes-member-equal-of-strip-cdrs
  (equal (in val (omap::values map))
         (and (member-equal val (strip-cdrs (omap::mfix map)))
              t))
  :induct t
  :enable (omap::values
           member-equal
           omap::mfix
           omap::mapp
           omap::emptyp
           omap::head
           omap::tail))

(defruled omap-values-becomes-strip-cdrs
  (equal (omap::values map)
         (mergesort (strip-cdrs (omap::mfix map))))
  :enable (set::expensive-rules
           in-of-omap-values-becomes-member-equal-of-strip-cdrs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The omap mirrors of the oset splitting laws in @(see oset). An omap is a
;; strictly increasing alist, so the same three facts hold of it, read on the
;; @(tsee car)s of its pairs.

(defruled omapp-of-cdr-when-omapp
  (implies (omap::mapp l)
           (omap::mapp (cdr l)))
  :enable omap::mapp)

;; Splitting an omap: both halves of an append are omaps themselves.

(defruled omapp-of-prefix-when-omapp-of-append
  (implies (and (true-listp x)
                (omap::mapp (append x y)))
           (omap::mapp x))
  :induct t
  :enable (omap::mapp
           append))

(defruled omapp-of-suffix-when-omapp-of-append
  (implies (omap::mapp (append x y))
           (omap::mapp y))
  :induct (append x y)
  :enable (omap::mapp
           append))

;; An omap is strictly increasing on keys, so its first key is below every
;; later key, and every key of a prefix is below the first key of what
;; follows.

(defruled <<-of-caar-when-assoc-equal-of-cdr
  (implies (and (omap::mapp l)
                (assoc-equal x (cdr l)))
           (<< (caar l) x))
  :induct t
  :enable (omap::mapp
           assoc-equal
           <<-rules))

(defruled <<-of-caars-when-omapp-of-append
  (implies (and (omap::mapp (append a b))
                (consp a)
                (consp b))
           (<< (caar a) (caar b)))
  :induct (append a b)
  :enable (omap::mapp
           append
           <<-rules))

(defruled <<-across-append-when-omapp
  (implies (and (omap::mapp (append a b))
                (assoc-equal x a)
                (consp b))
           (<< x (caar b)))
  :induct (append a b)
  :enable (omap::mapp
           append
           assoc-equal
           <<-rules
           <<-of-caars-when-omapp-of-append))

;; So every key of a prefix is below every key of what follows.

(defruled <<-across-append-of-keys-when-omapp
  (implies (and (omap::mapp (append a b))
                (assoc-equal x a)
                (assoc-equal y b))
           (<< x y))
  :cases ((equal y (caar b)))
  :use (<<-across-append-when-omapp
        (:instance omapp-of-suffix-when-omapp-of-append (x a) (y b))
        (:instance <<-of-caar-when-assoc-equal-of-cdr (l b) (x y)))
  :enable (assoc-equal
           <<-rules))

;; An omap has no duplicate keys, so no key is bound on both sides of an
;; append.

(defruled not-assoc-equal-of-prefix-when-omapp-of-append
  (implies (and (omap::mapp (append a b))
                (assoc-equal x b))
           (not (assoc-equal x a)))
  :use (:instance <<-across-append-of-keys-when-omapp (y x))
  :enable <<-rules)

(defruled not-assoc-equal-of-suffix-when-omapp-of-append
  (implies (and (omap::mapp (append a b))
                (assoc-equal x a))
           (not (assoc-equal x b)))
  :enable not-assoc-equal-of-prefix-when-omapp-of-append)

;; Likewise, a binding in the tail is a binding anywhere but at the first key.
;; The omap mirror of @(tsee member-equal-of-cdr-when-osetp).

(defruled assoc-equal-of-cdr-when-omapp
  (implies (omap::mapp l)
           (equal (assoc-equal x (cdr l))
                  (if (equal x (caar l))
                      nil
                    (assoc-equal x l))))
  :use (:instance <<-of-caar-when-assoc-equal-of-cdr
                  (x (caar l)))
  :enable (omap::mapp
           assoc-equal
           <<-rules))

;; The first and last elements of a nonempty omap are pairs, not @('nil').

(defruled car-under-iff-when-omapp
  (implies (omap::mapp l)
           (iff (car l)
                (consp l)))
  :enable omap::mapp)

(defruled car-of-last-under-iff-when-omapp
  (implies (omap::mapp l)
           (iff (car (last l))
                (consp l)))
  :induct (last l)
  :enable (last
           omap::mapp))

;; The first and last keys of an omap are bound to its first and last pairs,
;; and they differ unless the omap has a single pair.

(defruled assoc-equal-of-caar-when-omapp
  (implies (and (omap::mapp l)
                (consp l))
           (equal (assoc-equal (caar l) l)
                  (car l)))
  :enable (assoc-equal
           omap::mapp))

(defruled <<-of-caar-and-caar-of-last-when-omapp
  (implies (and (omap::mapp l)
                (consp (cdr l)))
           (<< (caar l) (caar (last l))))
  :induct (last l)
  :enable (last
           omap::mapp
           <<-rules))

(defruled equal-of-caar-of-last-and-caar-when-omapp
  (implies (omap::mapp l)
           (equal (equal (caar (last l)) (caar l))
                  (not (consp (cdr l)))))
  :use <<-of-caar-and-caar-of-last-when-omapp
  :enable (last
           <<-rules))

(defruled assoc-equal-of-caar-of-last-when-omapp
  (implies (and (omap::mapp l)
                (consp l))
           (equal (assoc-equal (caar (last l)) l)
                  (car (last l))))
  :induct (last l)
  :enable (last
           assoc-equal
           omap::mapp
           equal-of-caar-of-last-and-caar-when-omapp
           <<-rules))

;; Likewise, a binding in all but the last pair is a binding anywhere but at
;; the last key. The omap mirror of @(tsee member-equal-of-butlast-when-osetp).

(defruled assoc-equal-of-butlast-when-omapp
  (implies (omap::mapp l)
           (equal (assoc-equal x (butlast l 1))
                  (if (equal x (caar (last l)))
                      nil
                    (assoc-equal x l))))
  :induct (last l)
  :enable (last
           assoc-equal
           omapp-of-cdr-when-omapp
           equal-of-caar-of-last-and-caar-when-omapp))

;; A key of an omap is below whatever its last key is below, and above
;; whatever its first key is above.

(defrulel <<-of-caar-when-<<-of-caar-of-last
  (implies (and (omap::mapp l)
                (<< (caar (last l)) y))
           (<< (caar l) y))
  :induct (last l)
  :enable (last
           omap::mapp
           <<-rules))

(defruled <<-when-assoc-equal-and-<<-of-caar-of-last
  (implies (and (assoc-equal x l)
                (omap::mapp l)
                (<< (caar (last l)) y))
           (<< x y))
  :induct (last l)
  :enable (last
           assoc-equal
           omapp-of-cdr-when-omapp))

(defruled <<-when-assoc-equal-and-<<-of-arg1-and-caar
  (implies (and (assoc-equal y l)
                (omap::mapp l)
                (<< x (caar l)))
           (<< x y))
  :induct (assoc-equal y l)
  :enable (assoc-equal
           omap::mapp
           <<-rules))

;; So no key of an omap is below its first key or above its last.

(defruled not-<<-of-arg1-and-caar-when-assoc-equal
  (implies (and (assoc-equal x l)
                (omap::mapp l))
           (not (<< x (caar l))))
  :use (:instance <<-when-assoc-equal-and-<<-of-arg1-and-caar
                  (y x))
  :enable <<-rules)

(defruled not-<<-of-caar-of-last-when-assoc-equal
  (implies (and (assoc-equal x l)
                (omap::mapp l))
           (not (<< (caar (last l)) x)))
  :use (:instance <<-when-assoc-equal-and-<<-of-caar-of-last
                  (y x))
  :enable <<-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The head key of an omap is its least key, and deleting it leaves the tail.

(defruled head-key-becomes-head-of-keys
  (equal (mv-nth 0 (omap::head map))
         (set::head (omap::keys map)))
  :induct (omap::keys map)
  :enable (omap::keys
           omap::head-tail-order
           set::head-insert)
  :disable omap::update-of-head-and-tail)

(defruled delete-when-equal-of-head-key
  (implies (equal x (mv-nth 0 (omap::head map)))
           (equal (omap::delete x map)
                  (omap::tail map)))
  :enable omap::delete)
