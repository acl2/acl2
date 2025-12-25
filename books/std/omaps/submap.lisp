; Ordered Maps (Omaps) Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(include-book "core")
(include-book "with-fixing-theorems")
(include-book "assoc")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled assoc-when-submap-and-assoc
  (implies (and (submap sub sup)
                (assoc key sub))
           (equal (assoc key sub)
                  (assoc key sup)))
  :induct t
  :enable submap)

(defrule assoc-when-submap-and-assoc-syntaxp
  (implies (and (submap sub sup)
                (syntaxp (<< sup sub))
                (assoc key sub))
           (equal (assoc key sub)
                  (assoc key sup)))
  :by assoc-when-submap-and-assoc)

(defrule assoc-under-iff-when-submap-and-assoc
  (implies (and (submap sub sup)
                (assoc key sub))
           (assoc key sup))
  :disable assoc-when-submap-and-assoc
  :use assoc-when-submap-and-assoc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled submap-of-tail-when-submap
  (implies (submap sub sup)
           (submap (tail sub) sup))
  :enable submap)

(defrule submap-of-tail-when-submap-cheap
  (implies (submap sub sup)
           (submap (tail sub) sup))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by submap-of-tail-when-submap)

;;;;;;;;;;;;;;;;;;;;

(defruled submap-when-submap-of-arg1-and-tail
  (implies (submap sub (tail sup))
           (submap sub sup))
  :induct t
  :enable submap)

(defrule submap-when-submap-of-arg1-and-tail-cheap
  (implies (submap sub (tail sup))
           (submap sub sup))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by submap-when-submap-of-arg1-and-tail)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule reflexivity-of-submap
  (submap map map)
  :induct t
  :enable (submap
           assoc-of-head-key))

(defrule transitivity-of-submap
  (implies (and (submap x y)
                (submap y z))
           (submap x z))
  :induct t
  :enable (submap
           assoc-when-submap-and-assoc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This definition and theorems were taken from:
;;   projects/aleo/bft/library-extensions/omap-theorems.lisp

(define-sk submap-sk ((sub mapp) (sup mapp))
  (forall (key)
          (implies (omap::assoc key sub)
                   (equal (omap::assoc key sub)
                          (omap::assoc key sup))))
  :skolem-name submap-witness)

(defruledl submap-sk-of-tail-when-submap-sk
  (implies (submap-sk sub sup)
           (submap-sk (tail sub) sup))
  :expand (submap-sk (tail sub) sup)
  :use (:instance submap-sk-necc
                  (key (submap-witness (tail sub) sup))))

(defruledl submap-sk-when-submap
  (implies (submap sub sup)
           (submap-sk sub sup))
  :enable (submap-sk
           assoc-when-submap-and-assoc))

(defruledl submap-when-submap-sk
  (implies (submap-sk sub sup)
           (submap sub sup))
  :induct t
  :hints ('(:use (:instance submap-sk-necc
                            (key (mv-nth 0 (head sub))))))
  :enable (submap
           submap-sk-of-tail-when-submap-sk))

(defruled submap-to-submap-sk
  (equal (submap sub sup)
         (submap-sk sub sup))
  :use (submap-sk-when-submap
        submap-when-submap-sk))

;; Enable this ruleset to perform pick-a-point reasoning on SUBMAP.
;; The arbitrary element will be (SUBMAP-WITNESS <sub> <sup>),
;; where <sub> and <sup> are the omaps for which
;; we want to prove that (SUBMAP <sub> <sup>) holds.
(defthy pick-a-point
  '(submap-to-submap-sk
    submap-sk))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled head-key-minimal-2
  (implies (assoc key map)
           (not (<< key (mv-nth 0 (head map)))))
  :by head-key-minimal)

(defruled <<-of-head-head-when-submap
  (implies (and (submap x y)
                (not (emptyp x)))
           (not (<< (mv-nth 0 (head x))
                    (mv-nth 0 (head y)))))
  :enable head-key-minimal-2)

(defruled head-key-minimal-3
  (implies (assoc key (tail map))
           (<< (mv-nth 0 (head map)) key))
  :enable head-key-minimal-2
  :disable acl2::<<-trichotomy
  :use (:instance acl2::<<-trichotomy
                  (acl2::y key)
                  (acl2::x (mv-nth 0 (head map)))))

(defrule assoc-when-<<-head
  (implies (<< (mv-nth 0 (head map)) key)
           (equal (assoc key map)
                  (assoc key (tail map)))))

(defrule submap-membership-tail
  (implies (and (submap x y)
                (assoc key (tail x)))
           (assoc key (tail y)))
  :enable head-key-minimal-3
  :disable assoc-under-iff-when-submap-and-assoc
  :use (<<-of-head-head-when-submap
        (:instance assoc-under-iff-when-submap-and-assoc
                   (sub x)
                   (sup y))))

(defrule submap-membership-tail-2
  (implies (and (submap x y)
                (not (assoc a (tail y))))
           (not (assoc a (tail x))))
  :by submap-membership-tail)

(defruled submap-antisymmetry-head-key
  (implies (and (submap x y)
                (submap y x))
           (equal (mv-nth 0 (head x))
                  (mv-nth 0 (head y))))
  :use (<<-of-head-head-when-submap
        (:instance <<-of-head-head-when-submap
                   (x y)
                   (y x))))

(defruled submap-antisymmetry-head
  (implies (and (submap x y)
                (submap y x))
           (equal (head x)
                  (head y)))
  :use (submap-antisymmetry-head-key
        (:instance head-becomes-head-key-and-assoc
                   (map x))
        (:instance head-becomes-head-key-and-assoc
                   (map y)))
  :prep-lemmas
  ((defruled head-becomes-head-key-and-assoc
     (implies (not (emptyp map))
              (equal (head map)
                     (list (mv-nth 0 (head map))
                           (cdr (assoc (mv-nth 0 (head map)) map)))))
     :enable (head
              assoc))))

(defruled submap-antisymmetry-head-syntaxp
  (implies (and (submap x y)
                (syntaxp (<< y x))
                (submap y x))
           (equal (head x)
                  (head y)))
  :by submap-antisymmetry-head)

(defruledl assoc-tail-expand
  (equal (assoc a (tail map))
         (and (not (equal a (mv-nth 0 (head map))))
              (assoc a map))))

(defruledl double-containment-lemma-in-tail
  (implies (and (submap x y)
                (submap y x))
           (equal (assoc a (tail x))
                  (assoc a (tail y))))
  :cases ((assoc a (tail x)))
  :use ((:instance assoc-tail-expand
                   (map x))
        (:instance assoc-tail-expand
                   (map y))))

(defruled submap-tail-tail-when-submap-and-submap
  (implies (and (submap x y)
                (submap y x))
           (submap (tail x) (tail y)))
  :use ((:instance double-containment-lemma-in-tail
                   (a (submap-witness (tail x) (tail y)))))
  :enable pick-a-point)

;;;;;;;;;;;;;;;;;;;;

(defruled equal-when-not-emptyp-not-emptyp
  (implies (and (not (emptyp x))
                (not (emptyp y)))
           (equal (equal x y)
                  (and (equal (head x) (head y))
                       (equal (tail x) (tail y)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0))))

(defruled antisymmetry-of-submap-weak
  (implies (and (submap x y)
                (submap y x))
           (equal (mfix x)
                  (mfix y)))
  :induct (omap-induction2 x y)
  :enable (equal-when-not-emptyp-not-emptyp
           submap-antisymmetry-head-syntaxp
           submap-tail-tail-when-submap-and-submap))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled antisymmetry-of-submap
  (equal (and (submap x y)
              (submap y x))
         (equal (mfix x)
                (mfix y)))
  :use antisymmetry-of-submap-weak)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled double-containment-no-backchain-limit
  (implies (and (mapp x)
                (mapp y))
           (equal (equal x y)
                  (and (submap x y)
                       (submap y x))))
  :enable antisymmetry-of-submap)

(defruled double-containment
  (implies (and (mapp x)
                (mapp y))
           (equal (equal x y)
                  (and (submap x y)
                       (submap y x))))
  :by double-containment-no-backchain-limit)
