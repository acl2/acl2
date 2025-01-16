; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SBT")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "misc/total-order" :dir :system)

(include-book "setup")

(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A chain element is an object decorated with a boolean polarity, indicating
;; membership in either p or q. This polarity tracking is necessary since p and
;; q may overlap.
;; Note that we cannot define a fixer for chain elements, because `p` and `q`
;; may be unsatisfiable.
(define chain-elemp (x)
  (declare (xargs :type-prescription (booleanp (chain-elemp x))))
  (and (consp x)
       (booleanp (car x))
       (if (car x)
           (and (p (cdr x)) t)
         (and (q (cdr x)) t))))

(defrule consp-when-chain-elemp-compound-recognizer
  (implies (chain-elemp elem)
           (consp elem))
  :rule-classes :compound-recognizer
  :enable chain-elemp)

;; Constructor for chain-elemp
(define chain-elem (polarity val)
  :returns (chain-elem chain-elemp
                       :hyp (if polarity (p val) (q val))
                       :hints (("Goal" :in-theory (enable chain-elemp))))
  (cons (and polarity t) val))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define polarity ((elem consp))
  (declare (xargs :type-prescription (booleanp (polarity elem))))
  (and (car elem)
       t))

(defrule polarity-of-chain-elem
  (equal (polarity (chain-elem polarity val))
         (and polarity t))
  :enable (polarity chain-elem))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define val ((elem consp))
  (cdr elem))

(defrule val-of-chain-elem
  (equal (val (chain-elem polarity val))
         val)
  :enable (val chain-elem))

(defrule p-of-val-when-polarity
  (implies (and (chain-elemp x)
                (polarity x))
           (p (val x)))
  :enable (chain-elemp polarity val))

(defrule q-of-val-when-not-polarity
  (implies (and (chain-elemp x)
                (not (polarity x)))
           (q (val x)))
  :enable (chain-elemp polarity val))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled equal-when-chain-elemp
  (implies (and (chain-elemp x)
                (chain-elemp y))
           (equal (equal x y)
                  (and (equal (polarity x) (polarity y))
                       (equal (val x) (val y)))))
  :rule-classes ((:rewrite :backchain-limit-lst (1 1)))
  :enable (chain-elemp
           polarity
           val))

(defrule equal-when-chain-elemp-2
  (implies (and (chain-elemp x)
                (chain-elemp y)
                (equal (polarity x) (polarity y))
                (equal (val x) (val y)))
           (equal (equal x y) t))
  :rule-classes ((:rewrite :backchain-limit-lst (1 1 nil nil)))
  :enable equal-when-chain-elemp)

(defrule equal-of-chain-elem
  (equal (equal (chain-elem polarity1 x1)
                (chain-elem polarity2 x2))
         (and (iff polarity1 polarity2)
              (equal x1 x2)))
  :enable chain-elem)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Steps in chain sequences

(define chain-step
  ((elem consp))
  :returns (elem$ chain-elemp :hyp (chain-elemp elem))
  (let ((polarity (polarity elem)))
    (chain-elem (not polarity)
                (if polarity
                    (f (val elem))
                  (g (val elem))))))

(defrule polarity-chain-step
  (equal (polarity (chain-step elem))
         (not (polarity elem)))
  :enable chain-step)

(defrule val-of-chain-step
  (equal (val (chain-step elem))
         (if (polarity elem)
             (f (val elem))
           (g (val elem))))
  :enable chain-step)

;; Follows from injectivity of f ang g
(defrule injectivity-of-chain-step-when-chain-elemp
  (implies (and (chain-elemp x)
                (chain-elemp y))
           (equal (equal (chain-step x)
                         (chain-step y))
                  (equal x y)))
  :enable equal-when-chain-elemp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define chain-steps
  ((elem consp)
   (steps natp))
  :returns (elem$ chain-elemp :hyp (chain-elemp elem))
  (if (zp steps)
      elem
    (chain-steps (chain-step elem)
                 (- steps 1))))

(defrule chain-steps-of-arg1-and-0-cheap
  (implies (zp steps)
           (equal (chain-steps elem steps)
                  elem))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable chain-steps)

(defrule chain-steps-of-arg1-and-nfix
  (equal (chain-steps elem (nfix steps))
         (chain-steps elem steps))
  :enable (chain-steps nfix))

(defruled chain-steps-of-chain-step-becomes-chain-step-of-chain-steps
 (equal (chain-steps (chain-step elem) n)
        (chain-step (chain-steps elem n)))
 :induct t
 :enable (chain-steps
          chain-step))

(defrule chain-steps-of-chain-step
 (equal (chain-steps (chain-step elem) n)
        (chain-steps elem (+ 1 (nfix n))))
 :induct t
 :enable (chain-steps
          chain-step))

(defrule chain-step-of-chain-steps
 (equal (chain-step (chain-steps elem n))
        (chain-steps elem (+ 1 (nfix n))))
 :use chain-steps-of-chain-step-becomes-chain-step-of-chain-steps)

(defrule chain-steps-of-chain-steps
  (equal (chain-steps (chain-steps elem n) m)
         (chain-steps elem (+ (nfix n) (nfix m))))
 :induct t
 :enable (chain-steps nfix))

(defruled chain-steps-of-+
  (implies (and (natp n)
                (natp m))
           (equal (chain-steps elem (+ n m))
                  (chain-steps (chain-steps elem n) m))))

(theory-invariant
 (incompatible! (:rewrite chain-steps-of-chain-steps)
                (:rewrite chain-steps-of-+)))

(defruled commutativity-of-chain-steps
  (equal (chain-steps (chain-steps elem m) n)
         (chain-steps (chain-steps elem n) m)))

(defrule injectivity-of-chain-steps-on-arg1-when-chain-elemp
  (implies (and (chain-elemp x)
                (chain-elemp y))
           (equal (equal (chain-steps x n)
                         (chain-steps y n))
                  (equal x y)))
  :induct t
  :enable chain-steps)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A preorder over position in a chain
;; Note, it is not a partial order (i.e. not antisymmetric) because chains may
;; be cyclic.
;; Specifies that the latter chain element is reachable after some number of
;; steps taken from the former.
(define-sk chain<=
  ((x consp)
   y)
  (exists n
    (equal (chain-steps x (nfix n))
           y)))

(defrule chain<=-of-arg1-and-chain-steps
  (chain<= x (chain-steps x n))
  :use (:instance chain<=-suff (y (chain-steps x n))))

(defrule reflexivity-of-chain<=
  (chain<= x x)
  :disable (chain<=-of-arg1-and-chain-steps)
  :use (:instance chain<=-of-arg1-and-chain-steps (n 0)))

(defrule transitivity-of-chain<=
  (implies (and (chain<= x y)
                (chain<= y z))
           (chain<= x z))
  :expand ((chain<= x y)
           (chain<= y z)))

(defrule chain-elemp-when-chain<=-of-arg1-forward
  (implies (and (chain-elemp x)
                (chain<= x y))
           (chain-elemp y))
  :rule-classes ((:forward-chaining :trigger-terms ((chain<= x y))))
  :enable chain<=)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An equivalence relation based on membership within the same chain

;; Note: when the arguments are not chain-elemp, the relation becomes exact
;; equality. This is done so that chain= acts as an equivalence relation even
;; when the elements are outside of the intended domain.
(define chain=
  ((x consp)
   (y consp))
  (if (and (chain-elemp x)
           (chain-elemp y))
      (or (chain<= x y)
          (chain<= y x))
    (equal x y)))

(defrule chain=-when-chain<=-forward
  (implies (and (chain-elemp x)
                (chain<= x y))
           (chain= x y))
  :rule-classes ((:forward-chaining :trigger-terms ((chain<= x y))))
  :enable chain=)

(defrule reflexivity-of-chain=
  (chain= x x)
  :enable chain=)

(defrule symmetry-of-chain=
  (equal (chain= y x)
         (chain= x y))
  :enable chain=)

;; TODO: simplify these proofs
(defrule chain=-when-shared-chain<=-base
  (implies (and (chain-elemp x)
                (chain<= x y)
                (chain<= x z))
           (chain= y z))
  :enable (chain= nfix)
  :cases ((< (chain<=-witness x y)
             (chain<=-witness x z)))
  :expand ((chain<= x y)
           (chain<= x z))
  :prep-lemmas
  ((defrule chain<=-when-chain-steps-from-shared-base
     (implies (and (natp n)
                   (natp m)
                   (equal (chain-steps x n) y)
                   (equal (chain-steps x m) z)
                   (<= n m))
              (chain<= y z))
     :enable nfix
     :use (:instance chain<=-suff
                     (x y)
                     (y z)
                     (n (- m n))))))

(defrule chain=-when-shared-chain<=-of
  (implies (and (chain-elemp x)
                (chain-elemp y)
                (chain<= x z)
                (chain<= y z))
           (chain= x y))
  :enable (chain= nfix)
  :cases ((< (chain<=-witness x z)
             (chain<=-witness y z)))
  :expand ((chain<= x z)
           (chain<= y z))
  :prep-lemmas
  ((defrule chain<=-when-chain-steps-from-shared-end
     (implies (and (chain-elemp x)
                   (chain-elemp y)
                   (natp n)
                   (natp m)
                   (equal (chain-steps x n) z)
                   (equal (chain-steps y m) z)
                   (<= n m))
              (chain<= y x))
     :enable natp
     :disable chain-steps-of-chain-steps
     :use ((:instance chain<=-suff
                      (x y)
                      (y x)
                      (n (- m n)))
           (:instance chain-steps-of-+
                      (elem y)
                      (n (- m n))
                      (m n))))))

(defrule transitivity-of-chain=
  (implies (and (chain= x y)
                (chain= y z))
           (chain= x z))
  :enable chain=
  :use ((:instance chain=-when-shared-chain<=-base
                   (x y)
                   (y x)
                   (z z))
        (:instance chain=-when-shared-chain<=-of
                   (x x)
                   (y z)
                   (z y))))

(defequiv chain=)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Definedness of inverses via chain membership

(defruled exists-f-inverse-of-chain-elem-when-chain-steps
  (implies (and (chain-elemp x)
                (posp n)
                (equal (chain-steps x n) y)
                (not (polarity y)))
           (exists-f-inverse (val y)))
  :induct t
  :enable chain-steps)

(defruled exists-f-inverse-of-chain-elem-when-chain<=
  (implies (and (chain-elemp x)
                (chain<= x y)
                (polarity x)
                (not (polarity y)))
           (exists-f-inverse (val y)))
  :use (:instance exists-f-inverse-of-chain-elem-when-chain-steps
                  (n (chain<=-witness x y)))
  :enable chain<=)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled exists-g-inverse-of-chain-elem-when-chain-steps
  (implies (and (chain-elemp x)
                (posp n)
                (equal (chain-steps x n) y)
                (polarity y))
           (exists-g-inverse (val y)))
  :induct t
  :enable chain-steps)

(defruled exists-g-inverse-of-chain-elem-when-chain<=
  (implies (and (chain-elemp x)
                (chain<= x y)
                (not (polarity x))
                (polarity y))
           (exists-g-inverse (val y)))
  :use (:instance exists-g-inverse-of-chain-elem-when-chain-steps
                  (n (chain<=-witness x y)))
  :enable chain<=)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Initial chain elements

(define initialp ((elem consp))
  (if (polarity elem)
      (not (exists-g-inverse (val elem)))
    (not (exists-f-inverse (val elem)))))

;; TODO: forward to nil?
(defrule equal-when-chain<=-initial
  (implies (and (chain-elemp elem)
                (initialp initial)
                (equal (chain-steps elem n) initial))
           (equal elem initial))
  :rule-classes nil
  :induct t
  :enable (initialp
           chain-steps))

(defrule chain<=-of-arg1-and-initial
  (implies (and (chain-elemp elem)
                (initialp initial))
           (equal (chain<= elem initial)
                  (equal elem initial)))
  :enable chain<=
  :cases ((equal elem initial))
  :use (:instance equal-when-chain<=-initial
                  (n (chain<=-witness elem initial))))

(defruled chain<=-of-initial-and-arg2
  (implies (and (chain-elemp elem)
                (chain-elemp initial)
                (initialp initial))
           (equal (chain<= initial elem)
                  (chain= initial elem)))
  :enable chain=)

(theory-invariant
 (incompatible! (:rewrite chain<=-of-initial-and-arg2)
                (:definition chain=)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initial-wrt
  ((initial consp)
   (elem consp))
  (declare (xargs :type-prescription (booleanp (initial-wrt initial elem))))
  (and (chain-elemp initial)
       (initialp initial)
       (chain<= initial elem)))

(defrule chain-elemp-of-arg1-when-initial-wrt-forward
  (implies (initial-wrt x y)
           (chain-elemp x))
  :rule-classes :forward-chaining
  :enable initial-wrt)

(defrule chain-elemp-of-arg2-when-initial-wrt-forward
  (implies (initial-wrt x y)
           (chain-elemp y))
  :rule-classes :forward-chaining
  :enable initial-wrt)

(defrule initialp-when-initial-wrt-forward
  (implies (initial-wrt x y)
           (initialp x))
  :rule-classes :forward-chaining
  :enable initial-wrt)

(defrule chain<=-when-initial-wrt-forward
  (implies (initial-wrt x y)
           (chain<= x y))
  :rule-classes :forward-chaining
  :enable initial-wrt)

(defruled uniquenss-of-initial-wrt
  (implies (initial-wrt initial1 x)
           (equal (initial-wrt initial2 x)
                  (equal initial1 initial2)))
  :enable initial-wrt
  :disable transitivity-of-chain=
  :expand (chain= initial1 initial2)
  :use ((:instance transitivity-of-chain=
                   (x initial1)
                   (y x)
                   (z initial2))
        (:instance chain<=-of-initial-and-arg2
                   (initial initial2)
                   (elem x))))

(defrule initial-wrt-under-chain=
  (implies (chain= x y)
           (equal (initial-wrt initial x)
                  (initial-wrt initial y)))
  :rule-classes :congruence
  :enable (initial-wrt
           chain<=-of-initial-and-arg2)
  :use lemma
  :prep-lemmas
  ((defruled lemma
     (implies (and (or (not (chain-elemp x))
                       (not (chain-elemp y)))
                   (chain= x y))
              (equal (initial-wrt initial x)
                     (initial-wrt initial y)))
     :enable (initial-wrt chain=))))

(defrule reflexivity-of-initial-wrt-when-initial-wrt
  (implies (initial-wrt initial x)
           (initial-wrt initial initial))
  :rule-classes :forward-chaining
  :enable initial-wrt)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Of course, not all chains have initial elements, since chains may be
;; cyclic or backwards-infinite (chains are always forward-infinite).
(defchoose get-initial (initial) (elem)
  (initial-wrt initial elem))

(define exists-initial ((elem consp))
  (and (chain-elemp (get-initial elem))
       (initial-wrt (get-initial elem) elem)))

(defrule chain-elemp-of-get-initial-when-exists-initial
  (implies (exists-initial elem)
           (chain-elemp (get-initial elem)))
  :enable (exists-initial initial-wrt))

(defrule initialp-of-get-initial-when-exists-initial
  (implies (exists-initial elem)
           (initialp (get-initial elem)))
  :enable (exists-initial initial-wrt))

(defrule chain=-of-get-initial-when-exists-initial
  (implies (exists-initial elem)
           (chain= (get-initial elem) elem))
  :enable (exists-initial initial-wrt))

(defrule chain<=-of-get-initial-when-exists-initial
  (implies (exists-initial elem)
           (chain<= (get-initial elem) elem))
  :enable exists-initial)

(defrule chain-elemp-when-exists-initial-forward
  (implies (exists-initial elem)
           (chain-elemp elem))
  :rule-classes :forward-chaining
  :enable exists-initial)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: this is disabled because it is soon "bootstrapped" into a version
;; with less hypotheses.
(defruled get-initial-under-chain=-when-exists-initials
  (implies (and (exists-initial x)
                (exists-initial y)
                (chain= x y))
           (equal (get-initial x)
                  (get-initial y)))
  :enable exists-initial
  :use (:instance uniquenss-of-initial-wrt
                  (x y)
                  (initial1 (get-initial x))
                  (initial2 (get-initial y))))

(defrule equal-get-initial-when-initial-wrt
  (implies (initial-wrt initial elem)
           (equal (get-initial elem) initial))
  :enable uniquenss-of-initial-wrt
  :use get-initial)

(defrule exists-initial-when-initial-wrt-forward
  (implies (initial-wrt initial elem)
           (exists-initial elem))
  :rule-classes :forward-chaining
  :enable exists-initial)

(defrule exists-initial-when-initialp-forward
  (implies (and (chain-elemp initial)
                (initialp initial))
           (exists-initial initial))
  :rule-classes ((:forward-chaining :trigger-terms ((initialp initial))))
  :enable initial-wrt
  :disable exists-initial-when-initial-wrt-forward
  :use (:instance exists-initial-when-initial-wrt-forward
                  (initial initial)
                  (elem initial)))

(defrule exists-initial-under-chain=
  (implies (chain= x y)
           (equal (exists-initial x)
                  (exists-initial y)))
  :rule-classes :congruence
  :enable chain=
  :use ((:instance exists-initial-under-chain=-aux)
        (:instance exists-initial-under-chain=-aux
                   (x y)
                   (y x)))
  :prep-lemmas
  ((defruled exists-initial-under-chain=-aux
     (implies (and (chain-elemp x)
                   (chain= x y)
                   (exists-initial y))
              (exists-initial x))
     :enable exists-initial)))


(defruled get-initial-under-chain=-when-exists-initial
  (implies (and (exists-initial x)
                (chain-elemp y)
                (chain= x y))
           (equal (get-initial x)
                  (get-initial y)))
  :use get-initial-under-chain=-when-exists-initials)

(defrule get-initial-under-chain=-when-exists-initial-syntaxp
  (implies (and (exists-initial x)
                (chain-elemp y)
                (chain= x y)
                ;; Prevents looping
                (syntaxp (<< y x)))
           (equal (get-initial x)
                  (get-initial y)))
  :use get-initial-under-chain=-when-exists-initial)

(defrule exists-g-inverse-when-not-exists-initial
  (implies (and (chain-elemp elem)
                (not (exists-initial elem))
                (polarity elem))
           (exists-g-inverse (val elem)))
  ;; :rule-classes ((:forward-chaining :trigger-terms ((exists-initial elem))))
  :enable initialp
  :use (:instance exists-initial-when-initialp-forward
                  (initial elem)))

(defrule exists-f-inverse-when-not-exists-initial
  (implies (and (chain-elemp elem)
                (not (exists-initial elem))
                (not (polarity elem)))
           (exists-f-inverse (val elem)))
  ;; :rule-classes ((:forward-chaining :trigger-terms ((exists-initial elem))))
  :enable initialp
  :use (:instance exists-initial-when-initialp-forward
                  (initial elem)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; "Stoppers" are chains with initial elements. A p-stopper is a chain whose
;; initial element has positive polarity (is in p), and q-stopper is one whose
;; initial element has negative polarity (is in q).

(define in-q-stopper ((elem consp))
  (and (exists-initial elem)
       (not (polarity (get-initial elem)))))

(defrule exists-initial-when-in-q-stopper-forward
  (implies (in-q-stopper elem)
           (exists-initial elem))
  :rule-classes :forward-chaining
  :enable in-q-stopper)

(defrule not-polarity-of-get-initial-when-in-q-stopper-forward
  (implies (in-q-stopper elem)
           (not (polarity (get-initial elem))))
  :rule-classes :forward-chaining
  :enable in-q-stopper)

(defrule exists-g-inverse-when-in-q-stopper
  (implies (and (in-q-stopper elem)
                (polarity elem))
           (exists-g-inverse (val elem)))
  :enable in-q-stopper
  :disable exists-g-inverse-of-chain-elem-when-chain<=
  :use (:instance exists-g-inverse-of-chain-elem-when-chain<=
                  (x (get-initial elem))
                  (y elem)))

(defrule exists-f-inverse-when-not-in-q-stopper
  (implies (and (chain-elemp elem)
                (not (in-q-stopper elem))
                (not (polarity elem)))
           (exists-f-inverse (val elem)))
  :enable in-q-stopper
  :disable exists-f-inverse-of-chain-elem-when-chain<=
  :use ((:instance exists-f-inverse-of-chain-elem-when-chain<=
                   (x (get-initial elem))
                   (y elem))
        (:instance exists-f-inverse-when-not-exists-initial)))

(defrule in-q-stopper-under-chain=
  (implies (chain= x y)
           (equal (in-q-stopper x)
                  (in-q-stopper y)))
  :rule-classes :congruence
  :enable in-q-stopper)
