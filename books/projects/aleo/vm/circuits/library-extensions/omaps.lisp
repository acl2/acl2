; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "std/omaps/core" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::assoc-of-supermap-when-submap
  (implies (and (omap::submap sub sup)
                (omap::assoc key sub))
           (equal (omap::assoc key sup)
                  (omap::assoc key sub)))
  :induct t
  :enable omap::submap)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::submap-of-update-right
  (implies (not (omap::assoc key map))
           (equal (omap::submap map (omap::update key val map2))
                  (omap::submap map map2)))
  :induct t
  :enable omap::submap)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::not-in-when-key-less
  (implies (or (omap::emptyp map)
               (<< key (mv-nth 0 (omap::head map))))
           (not (omap::assoc key map)))
  :induct t
  :enable (omap::assoc
           omap::head
           omap::tail
           omap::mapp
           omap::mfix
           omap::emptyp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::head-not-in-tail
  (implies (not (omap::emptyp map))
           (not (omap::assoc (mv-nth 0 (omap::head map))
                             (omap::tail map))))
  :enable omap::head-tail-order
  :use (:instance omap::not-in-when-key-less
                  (map (omap::tail map))
                  (key (mv-nth 0 (omap::head map)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::submap-of-tail-lemma
  (implies (and (not (omap::emptyp map))
                (omap::submap (omap::tail map)
                              (omap::tail map)))
           (omap::submap (omap::tail map) map))
  :enable omap::head-not-in-tail
  :use (:instance omap::submap-of-update-right
                  (key (mv-nth 0 (omap::head map)))
                  (map (omap::tail map))
                  (val (mv-nth 1 (omap::head map)))
                  (map2 (omap::tail map))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule omap::submap-reflexive
  (omap::submap map map)
  :induct t
  :enable (omap::submap
           omap::submap-of-tail-lemma))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::submap-of-tail
  (implies (not (omap::emptyp map))
           (omap::submap (omap::tail map) map))
  :enable omap::submap-of-tail-lemma)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::assoc-of-car-of-from-lists
  (implies (consp keys)
           (equal (omap::assoc (car keys) (omap::from-lists keys vals))
                  (cons (car keys) (car vals))))
  :enable omap::from-lists)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::assoc-of-car-of-supermap-of-from-lists
  (implies (and (consp keys)
                (omap::submap (omap::from-lists keys vals) map))
           (equal (omap::assoc (car keys) map)
                  (cons (car keys) (car vals))))
  :use (:instance omap::assoc-of-supermap-when-submap
                  (key (car keys))
                  (sub (omap::from-lists keys vals))
                  (sup map))
  :enable omap::assoc-of-car-of-from-lists)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::assoc-of-cadr-of-from-lists
  (implies (and (consp (cdr keys))
                (not (member-equal (car keys) (cdr keys))))
           (equal (omap::assoc (cadr keys) (omap::from-lists keys vals))
                  (cons (cadr keys) (cadr vals))))
  :enable omap::from-lists)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::assoc-of-cadr-of-supermap-of-from-lists
  (implies (and (consp (cdr keys))
                (not (member-equal (car keys) (cdr keys)))
                (omap::submap (omap::from-lists keys vals) map))
           (equal (omap::assoc (cadr keys) map)
                  (cons (cadr keys) (cadr vals))))
  :use (:instance omap::assoc-of-supermap-when-submap
                  (key (cadr keys))
                  (sub (omap::from-lists keys vals))
                  (sup map))
  :enable omap::assoc-of-cadr-of-from-lists)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::not-in-from-lists-when-not-member
  (implies (not (member-equal key keys))
           (not (omap::assoc key (omap::from-lists keys vals))))
  :induct t
  :enable omap::from-lists)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::submap-of-from-lists-of-cdr-cdr
  (implies (and (no-duplicatesp-equal keys)
                (consp keys))
           (omap::submap (omap::from-lists (cdr keys) (cdr vals))
                         (omap::from-lists keys vals)))
  :enable (omap::from-lists
           no-duplicatesp-equal
           omap::submap-of-update-right
           omap::not-in-from-lists-when-not-member))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::submap-transitive
  (implies (and (omap::submap map1 map2)
                (omap::submap map2 map3))
           (omap::submap map1 map3))
  :induct (omap::size map1)
  :enable (omap::size
           omap::submap
           omap::assoc-of-supermap-when-submap))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::submap-of-from-lists-of-cdr-cdr-when-submap-of-from-lists
  (implies (and (no-duplicatesp-equal keys)
                (omap::submap (omap::from-lists keys vals) map)
                (consp keys))
           (omap::submap (omap::from-lists (cdr keys) (cdr vals)) map))
  :use (omap::submap-of-from-lists-of-cdr-cdr
        (:instance omap::submap-transitive
                   (map1 (omap::from-lists (cdr keys) (cdr vals)))
                   (map2 (omap::from-lists keys vals))
                   (map3 map))))
