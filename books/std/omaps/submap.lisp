; Ordered Maps (Omaps) Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Grant Jurgensen (grant@kestrel.edu)
;          Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/utilities/polarity" :dir :system)

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

(define-sk submap-sk ((sub mapp) (sup mapp))
  :parents (submap)
  :short "An alternative definition of @(tsee submap) using a skolem function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This definition is sometimes preferable to @(tsee submap). In particular,
     to support @(see pick-a-point)-style reasoning."))
  (forall (key)
          (implies (assoc key sub)
                   (equal (assoc key sub)
                          (assoc key sup))))
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

(defsection pick-a-point
  :parents (omaps)
  :short "A theory to enable pick-a-point reasoning for @(see omaps)."
  :long
  (xdoc::topstring
   (xdoc::p
    "In contrast to the oset's @(see set::pick-a-point-subset-strategy),
     this theory does not rely on computed hints. It simply rewrites
     @(tsee submap) to the skolem-equivalent @(tsee submap-sk), and unfolds the
     definition to expose the arbitrary element."))

  (defruled submap-to-submap-sk
    (equal (submap sub sup)
           (submap-sk sub sup))
    :use (submap-sk-when-submap
          submap-when-submap-sk))

  (defthy pick-a-point
    '(submap-to-submap-sk
      submap-sk))

  (defruled submap-to-submap-sk-in-conclusion
    (implies (syntaxp (acl2::want-to-weaken (submap sub sup)))
             (equal (submap sub sup)
                    (submap-sk sub sup)))
    :by submap-to-submap-sk)

  ;; Variant of pick-a-point that attempts to avoid rewriting submap
  ;; hypotheses.
  (defthy pick-a-point-conclusion
    '(submap-to-submap-sk-in-conclusion
      submap-sk)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following proof of antisymmetry mirrors the osets proof.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The minimal key (the head) of x cannot be smaller than the minimal head of
;; y. Since x is a submap of y, the head of x must be in y as well. Then the
;; head of y is either the head of x (in which case it is obviously not
;; smaller) or it is greater than y's minimal key.
(defruled <<-of-head-head-when-submap
  (implies (and (submap x y)
                (not (emptyp x)))
           (not (<< (mv-nth 0 (head x))
                    (mv-nth 0 (head y)))))
  :enable head-key-minimal-2)

;; Since key is in (tail x), it must be greater than the head of x. By the
;; previous theorem, it must also be greater than the head of y. Since it is in
;; y (by the submap hypothesis), it must be in y's tail.
(defrule assoc-of-tail-when-submap-and-assoc-of-tail
  (implies (and (submap x y)
                (assoc key (tail x)))
           (assoc key (tail y)))
  :enable head-key-minimal-3
  :disable assoc-under-iff-when-submap-and-assoc
  :use (<<-of-head-head-when-submap
        (:instance assoc-under-iff-when-submap-and-assoc
                   (sub x)
                   (sup y))))

(defrule assoc-of-tail-when-submap-and-not-assoc-of-tail
  (implies (and (submap x y)
                (not (assoc a (tail y))))
           (not (assoc a (tail x))))
  :by assoc-of-tail-when-submap-and-assoc-of-tail)

(defruledl submap-antisymmetry-head-key
  (implies (and (submap x y)
                (submap y x))
           (equal (mv-nth 0 (head x))
                  (mv-nth 0 (head y))))
  :use (<<-of-head-head-when-submap
        (:instance <<-of-head-head-when-submap
                   (x y)
                   (y x))))

(defruledl submap-antisymmetry-head
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

(defruledl submap-antisymmetry-head-syntaxp
  (implies (and (submap x y)
                (syntaxp (<< y x))
                (submap y x))
           (equal (head x)
                  (head y)))
  :by submap-antisymmetry-head)

(defruledl submap-antisymmetry-assoc-of-tail
  (implies (and (submap x y)
                (submap y x))
           (equal (assoc a (tail x))
                  (assoc a (tail y))))
  :cases ((assoc a (tail x)))
  :use ((:instance assoc-tail-expand
                   (map x))
        (:instance assoc-tail-expand
                   (map y)))
  :prep-lemmas
  ((defruled assoc-tail-expand
     (equal (assoc a (tail map))
            (and (not (equal a (mv-nth 0 (head map))))
                 (assoc a map))))))

(defruledl submap-antisymmetry-tail
  (implies (and (submap x y)
                (submap y x))
           (submap (tail x) (tail y)))
  :use ((:instance submap-antisymmetry-assoc-of-tail
                   (a (submap-witness (tail x) (tail y)))))
  :enable pick-a-point)

;;;;;;;;;;;;;;;;;;;;

(defruled equal-when-not-emptyp-not-emptyp-cheap
  (implies (and (not (emptyp x))
                (not (emptyp y)))
           (equal (equal x y)
                  (and (equal (head x) (head y))
                       (equal (tail x) (tail y)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0))))

;; We induct over both maps simultaneously. At each step, we show the heads
;; must be the same.
(defruled antisymmetry-of-submap-weak
  (implies (and (submap x y)
                (submap y x))
           (equal (mfix x)
                  (mfix y)))
  :induct (omap-induction2 x y)
  :enable (equal-when-not-emptyp-not-emptyp-cheap
           submap-antisymmetry-head-syntaxp
           submap-antisymmetry-tail))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled antisymmetry-of-submap
  (equal (and (submap x y)
              (submap y x))
         (equal (mfix x)
                (mfix y)))
  :use antisymmetry-of-submap-weak)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection double-containment
  :parents (omaps)
  :short "Prove omap equality by antisymmetry of @(tsee submap)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the equivalent of @(see set::double-containment) for
     @(see omaps). See also @(see extensionality) (it may be more
     straightforward to enable @('extensionality') than to enable both
     @('double-containment') and @('pick-a-point'))."))

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
    :rule-classes ((:rewrite :backchain-limit-lst (1 1)))
    :by double-containment-no-backchain-limit))
