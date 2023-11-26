; Author: Grant Jurgensen (grant@kestrel.edu)

(in-package "SB")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "misc/total-order" :dir :system)

(include-book "setup")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A chain element is an object decorated with a boolean polarity, indicating
;; membership in either p or q. This polarity tracking is necessary since p and
;; q may overlap.
(define chain-elem-p (x)
  :returns (is-chain-elem booleanp)
  (and (consp x)
       (booleanp (car x))
       (if (car x)
           (and (p (cdr x)) t)
         (and (q (cdr x)) t))))

(defrule consp-when-chain-elem-p-compound-recognizer
  (implies (chain-elem-p x)
           (consp x))
  :enable (chain-elem-p)
  :rule-classes :compound-recognizer)

(define make-chain-elem (polarity x)
  :guard (if polarity (p x) (q x))
  :returns (chain-elem chain-elem-p
                       :hyp :guard
                       :hints (("Goal" :in-theory (enable chain-elem-p))))
  (cons (and polarity t) x))


(define polarity ((x consp))
  (car x))

(defrule booleanp-of-polarity-when-chain-elem-p
  (implies (chain-elem-p x)
           (booleanp (polarity x)))
  :enable (chain-elem-p polarity)
  :rule-classes ((:type-prescription) (:forward-chaining)))

(defrule polarity-of-make-chain-elem
  (equal (polarity (make-chain-elem polarity x))
         (and polarity t))
  :enable (polarity make-chain-elem))


(define chain-elem ((x consp))
  (cdr x))

(defrule in-chain-elem-of-x-when-chain-elem-p-forward
  (implies (chain-elem-p x)
           (if (polarity x)
               (p (chain-elem x))
             (q (chain-elem x))))
  :enable (chain-elem-p polarity chain-elem)
  :rule-classes :forward-chaining)

(defrule chain-elem-of-make-chain-elem
  (equal (chain-elem (make-chain-elem polarity x))
         x)
  :enable (chain-elem make-chain-elem))


(defrule p-of-chain-elem-when-polarity
  (implies (and (chain-elem-p x)
                (polarity x))
           (p (chain-elem x))))

(defrule q-of-chain-elem-when-not-polarity
  (implies (and (chain-elem-p x)
                (not (polarity x)))
           (q (chain-elem x))))

(defruled equal-when-chain-elem-p
  (implies (and (chain-elem-p x)
                (chain-elem-p y))
           (equal (equal x y)
                  (and (equal (polarity x) (polarity y))
                       (equal (chain-elem x) (chain-elem y)))))
  :enable (chain-elem-p
           polarity
           chain-elem)
  :rule-classes ((:rewrite :backchain-limit-lst (1 1))))

(defrule equal-when-chain-elem-p-2
  (implies (and (chain-elem-p x)
                (chain-elem-p y)
                (equal (polarity x) (polarity y))
                (equal (chain-elem x) (chain-elem y)))
           (equal (equal x y) t))
  :enable (equal-when-chain-elem-p)
  :rule-classes ((:rewrite :backchain-limit-lst (1 1 nil nil))))

(defrule equal-of-make-chain-elem
  (equal (equal (make-chain-elem polarity1 x1)
                (make-chain-elem polarity2 x2))
         (and (iff polarity1 polarity2)
              (equal x1 x2)))
  :enable (make-chain-elem))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Steps in chain sequences

(define chain-step
  ((x chain-elem-p))
  :returns (chain-elem chain-elem-p :hyp :guard)
  (let ((polarity (polarity x)))
    (make-chain-elem (not polarity)
                     (if polarity
                         (f (chain-elem x))
                       (g (chain-elem x))))))


(defrule polarity-chain-step
  (equal (polarity (chain-step x))
         (not (polarity x)))
  :enable chain-step)

(defrule chain-elem-of-chain-step
  (equal (chain-elem (chain-step x))
         (if (polarity x)
             (f (chain-elem x))
           (g (chain-elem x))))
  :enable (chain-step))

;; Follows from injectivity of f ang g
(defrule injectivity-of-chain-step-when-chain-elem-p
  (implies (and (chain-elem-p x)
                (chain-elem-p y))
           (equal (equal (chain-step x)
                         (chain-step y))
                  (equal x y)))
  :enable (equal-when-chain-elem-p))


(define chain-steps
  ((x chain-elem-p)
   (steps natp))
  :returns (stepped chain-elem-p :hyp (chain-elem-p x))
  (if (zp steps)
      x
    (chain-steps (chain-step x) (- steps 1))))


(defrule chain-steps-of-arg1-and-0
  (implies (zp steps)
           (equal (chain-steps x steps)
                  x))
  :enable (chain-steps)
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defrule chain-steps-of-chain-step
 (equal (chain-steps (chain-step x) n)
        (chain-step (chain-steps x n)))
 :enable (chain-steps
          chain-step))

;; Note: backchain limit has to be 0, or else we may end up splitting on zp
(defrule chain-steps-of-arg1-and-not-zp-cheap
  (implies (not (zp steps))
           (equal (chain-steps x steps)
                  (chain-step (chain-steps x (- steps 1)))))
  :enable (chain-steps)
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defrule chain-steps-of-+
 (implies (and (natp n)
               (natp m))
          (equal (chain-steps x (+ n m))
                 (chain-steps (chain-steps x n) m)))
 :disable (chain-steps-of-chain-step
           chain-steps-of-arg1-and-not-zp-cheap)
 :enable (chain-steps))

(defrule commutativity-of-chain-steps
 (equal (chain-steps (chain-steps x m) n)
        (chain-steps (chain-steps x n) m))
 :use ((:instance chain-steps-of-+)
       (:instance chain-steps-of-+
                  (m n)
                  (n m))))

(defrule injectivity-of-chain-steps-on-arg1-when-chain-elem-p
  (implies (and (chain-elem-p x)
                (chain-elem-p y))
           (equal (equal (chain-steps x n)
                         (chain-steps y n))
                  (equal x y)))
  :enable (chain-steps))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A preorder over position in a chain
;; Note, it is not a partial order (i.e. not antisymmetric) because chains may
;; be cyclic.

;; Specifies that the latter chain element is reachable after some number of
;; steps taken from the former.
(define-sk chain<=
  ((x chain-elem-p)
   (y chain-elem-p))
  (exists n
    (equal (chain-steps x (nfix n)) y)))


(defrule chain<=-of-arg1-and-chain-steps
  (chain<= x (chain-steps x n))
  :use ((:instance chain<=-suff (y (chain-steps x n)))))

(defrule reflexivity-of-chain<=
  (chain<= x x)
  :disable (chain<=-of-arg1-and-chain-steps)
  :use (:instance chain<=-of-arg1-and-chain-steps (n 0)))

(defrule transitivity-of-chain<=
  (implies (and (chain<= x y)
                (chain<= y z))
           (chain<= x z))
  :expand ((chain<= x y)
           (chain<= y z))
  :disable (chain-steps-of-arg1-and-not-zp-cheap)
  :use ((:instance chain<=-suff
                   (y z)
                   (n (+ (chain<=-witness x y)
                         (chain<=-witness y z))))))

(defrule chain-elem-p-when-chain<=-of-arg1-forward
  (implies (and (chain-elem-p x)
                (chain<= x y))
           (chain-elem-p y))
  :enable (chain<=)
  :rule-classes ((:forward-chaining :trigger-terms ((chain<= x y)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An equivalence relation based on membership within the same chain

;; Note: when the arguments are not chain-elem-p, the relation becomes exact
;; equality. This is done so that chain= acts as an equivalence relation even
;; when the elements are outside of the intended domain. Ordinarily, we would
;; just force the elements into the domain with a fixing function, but such a
;; function is not easily defined without modifying our notion of
;; chain-elem-p. As it is now, chain-elem-p may be vacuous (iff p or q are
;; vacuous), so there may not exist some arbitrary value to map to.
(define chain=
  ((x chain-elem-p)
   (y chain-elem-p))
  (if (mbt (and (chain-elem-p x)
                (chain-elem-p y)))
      (or (chain<= x y)
          (chain<= y x))
    (equal x y)))


(defrule chain=-when-chain<=-forward
  (implies (and (chain-elem-p x)
                (chain<= x y))
           (chain= x y))
  :enable (chain=)
  :rule-classes ((:forward-chaining :trigger-terms ((chain<= x y)))))


(defrule reflexivity-of-chain=
  (chain= x x)
  :enable (chain=))

(defrule symmetry-of-chain=
  (equal (chain= y x)
         (chain= x y))
  :enable (chain=))


(defrule chain=-when-shared-chain<=-base
  (implies (and (chain-elem-p x)
                (chain<= x y)
                (chain<= x z))
           (chain= y z))
  :cases ((< (chain<=-witness x y)
             (chain<=-witness x z)))
  :expand ((chain<= x y)
           (chain<= x z))
  :enable (chain=)
  :prep-lemmas
  ((defrule chain<=-when-chain-steps-from-shared-base
     (implies (and (natp n)
                   (natp m)
                   (equal (chain-steps x n) y)
                   (equal (chain-steps x m) z)
                   (<= n m))
              (chain<= y z))
     :use ((:instance chain<=-suff
                      (x y)
                      (y z)
                      (n (- m n)))
           (:instance chain-steps-of-+
                      (n n)
                      (m (- m n)))))))

(defrule chain=-when-shared-chain<=-of
  (implies (and (chain-elem-p x)
                (chain-elem-p y)
                (chain<= x z)
                (chain<= y z))
           (chain= x y))
  :cases ((< (chain<=-witness x z)
             (chain<=-witness y z)))
  :expand ((chain<= x z)
           (chain<= y z))
  :enable (chain=)
  :prep-lemmas
  ((defrule chain<=-when-chain-steps-from-shared-end
     (implies (and (chain-elem-p x)
                   (chain-elem-p y)
                   (natp n)
                   (natp m)
                   (equal (chain-steps x n) z)
                   (equal (chain-steps y m) z)
                   (<= n m))
              (chain<= y x))
     :disable (commutativity-of-chain-steps)
     :use ((:instance chain<=-suff
                      (x y)
                      (y x)
                      (n (- m n)))
           (:instance chain-steps-of-+
                      (x y)
                      (n (- m n))
                      (m n))))))

(defrule transitivity-of-chain=
  (implies (and (chain= x y)
                (chain= y z))
           (chain= x z))
  :enable (chain=)
  :use ((:instance chain=-when-shared-chain<=-base
                   (x y)
                   (y x)
                   (z z))
        (:instance chain=-when-shared-chain<=-of
                   (x x)
                   (y z)
                   (z y))))

(defequiv chain=)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Definedness of inverses via chain membership

(defruled has-f-inverse-of-chain-elem-when-chain-steps
  (implies (and (chain-elem-p x)
                (posp n)
                (equal (chain-steps x n) y)
                (not (polarity y)))
           (has-f-inverse (chain-elem y)))
  :enable (chain-steps))

(defruled has-f-inverse-of-chain-elem-when-chain<=
  (implies (and (chain-elem-p x)
                (chain<= x y)
                (polarity x)
                (not (polarity y)))
           (has-f-inverse (chain-elem y)))
  :disable (chain-steps-of-arg1-and-not-zp-cheap)
  :use ((:instance has-f-inverse-of-chain-elem-when-chain-steps
                   (n (chain<=-witness x y))))
  :enable (chain<=))


(defruled has-g-inverse-of-chain-elem-when-chain-steps
  (implies (and (chain-elem-p x)
                (posp n)
                (equal (chain-steps x n) y)
                (polarity y))
           (has-g-inverse (chain-elem y)))
  :enable (chain-steps))

(defruled has-g-inverse-of-chain-elem-when-chain<=
  (implies (and (chain-elem-p x)
                (chain<= x y)
                (not (polarity x))
                (polarity y))
           (has-g-inverse (chain-elem y)))
  :disable (has-g-inverse-of-chain-elem-when-chain-steps
            chain-steps-of-arg1-and-not-zp-cheap)
  :use ((:instance has-g-inverse-of-chain-elem-when-chain-steps
                   (n (chain<=-witness x y))))
  :enable (chain<=))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Initial chain elements

(define initial-p ((x chain-elem-p))
  (if (polarity x)
      (not (has-g-inverse (chain-elem x)))
    (not (has-f-inverse (chain-elem x)))))


;; TODO: forward to nil?
(defrule equal-when-chain<=-initial
  (implies (and (chain-elem-p x)
                (initial-p initial)
                (equal (chain-steps x n) initial))
           (equal x initial))
  :enable (initial-p
           chain-steps)
  :rule-classes nil)

(defrule chain<=-of-arg1-and-initial
  (implies (and (chain-elem-p x)
                (initial-p initial))
           (equal (chain<= x initial)
                  (equal x initial)))
  :enable (chain<=)
  :cases ((equal x initial))
  :use ((:instance equal-when-chain<=-initial
                   (n (chain<=-witness x initial)))))

(defruled chain<=-of-initial-and-arg2
  (implies (and (chain-elem-p x)
                (chain-elem-p initial)
                (initial-p initial))
           (equal (chain<= initial x)
                  (chain= initial x)))
  :enable (chain=))

(theory-invariant
 (incompatible! (:rewrite chain<=-of-initial-and-arg2)
                (:definition chain=)))


(define initial-wrt (initial (x chain-elem-p))
  (and (chain-elem-p initial)
       (initial-p initial)
       (chain<= initial x)))


(defrule chain-elem-p-of-arg1-when-initial-wrt-forward
  (implies (initial-wrt x y)
           (chain-elem-p x))
  :enable (initial-wrt)
  :rule-classes :forward-chaining)

(defrule chain-elem-p-of-arg2-when-initial-wrt-forward
  (implies (initial-wrt x y)
           (chain-elem-p y))
  :enable (initial-wrt)
  :rule-classes :forward-chaining)

(defrule initial-p-when-initial-wrt-forward
  (implies (initial-wrt x y)
           (initial-p x))
  :enable (initial-wrt)
  :rule-classes :forward-chaining)

(defrule chain<=-when-initial-wrt-forward
  (implies (initial-wrt x y)
           (chain<= x y))
  :enable (initial-wrt)
  :rule-classes :forward-chaining)


(defruled uniquenss-of-initial-wrt
  (implies (initial-wrt initial1 x)
           (equal (initial-wrt initial2 x)
                  (equal initial1 initial2)))
  :disable (transitivity-of-chain=)
  :use ((:instance transitivity-of-chain=
                   (x initial1)
                   (y x)
                   (z initial2))
        (:instance chain<=-of-initial-and-arg2
                   (initial initial2)
                   (x x)))
  :enable (initial-wrt)
  :expand (chain= initial1 initial2))


(defrule initial-wrt-under-chain=
  (implies (chain= x y)
           (equal (initial-wrt initial x)
                  (initial-wrt initial y)))
  :enable (initial-wrt
           chain<=-of-initial-and-arg2)
  :use lemma
  :rule-classes :congruence
  :prep-lemmas
  ((defruled lemma
     (implies (and (or (not (chain-elem-p x))
                       (not (chain-elem-p y)))
                   (chain= x y))
              (equal (initial-wrt initial x)
                     (initial-wrt initial y)))
     :enable (initial-wrt chain=))))

(defrule reflexivity-of-initial-wrt-when-initial-wrt
  (implies (initial-wrt initial x)
           (initial-wrt initial initial))
  :enable (initial-wrt)
  :rule-classes :forward-chaining)


;; Of course, not all chains have initial elements, since chains may be
;; cyclic or backwards-infinite (chains are always forward-infinite).
(defchoose get-initial (initial) (x)
  (initial-wrt initial x))

(define has-initial ((x chain-elem-p))
  (initial-wrt (get-initial x) x))


(defrule chain-elem-p-of-get-initial-when-has-initial
  (implies (has-initial x)
           (chain-elem-p (get-initial x)))
  :enable (has-initial initial-wrt))

(defrule initial-p-of-get-initial-when-has-initial
  (implies (has-initial x)
           (initial-p (get-initial x)))
  :enable (has-initial initial-wrt))

(defrule chain=-of-get-initial-when-has-initial
  (implies (has-initial x)
           (chain= (get-initial x) x))
  :enable (has-initial initial-wrt))

(defrule chain<=-of-get-initial-when-has-initial
  (implies (has-initial x)
           (chain<= (get-initial x) x))
  :enable (has-initial))

(defrule chain-elem-p-when-has-initial-forward
  (implies (has-initial x)
           (chain-elem-p x))
  :enable (has-initial)
  :rule-classes :forward-chaining)


;; Note: this is disabled because it is soon "bootstrapped" into a version
;; with less hypotheses.
(defruled get-initial-under-chain=-when-has-initials
  (implies (and (has-initial x)
                (has-initial y)
                (chain= x y))
           (equal (get-initial x)
                  (get-initial y)))
  :enable (has-initial)
  :disable (uniquenss-of-initial-wrt)
  :use ((:instance uniquenss-of-initial-wrt
                   (x y)
                   (initial1 (get-initial x))
                   (initial2 (get-initial y)))))

(defrule equal-get-initial-when-initial-wrt
  (implies (initial-wrt initial x)
           (equal (get-initial x) initial))
  :enable (uniquenss-of-initial-wrt)
  :use get-initial)

(defrule has-initial-when-initial-wrt-forward
  (implies (initial-wrt initial x)
           (has-initial x))
  :enable (has-initial)
  :rule-classes :forward-chaining)

(defrule has-initial-when-initial-p-forward
  (implies (and (chain-elem-p x)
                (initial-p x))
           (has-initial x))
  :enable (initial-wrt)
  :use ((:instance has-initial-when-initial-wrt-forward
                   (initial x)))
  :rule-classes ((:forward-chaining :trigger-terms ((initial-p x)))))


(defrule has-initial-under-chain=
  (implies (chain= x y)
           (equal (has-initial x)
                  (has-initial y)))
  :enable (chain=)
  :use ((:instance has-initial-under-chain=-aux)
        (:instance has-initial-under-chain=-aux
                   (x y)
                   (y x)))
  :rule-classes :congruence
  :prep-lemmas
  ((defruled has-initial-under-chain=-aux
     (implies (and (chain-elem-p x)
                   (chain= x y)
                   (has-initial y))
              (has-initial x))
     :enable (has-initial))))


(defruled get-initial-under-chain=-when-has-initial
  (implies (and (has-initial x)
                (chain-elem-p y)
                (chain= x y))
           (equal (get-initial x)
                  (get-initial y)))
  :use get-initial-under-chain=-when-has-initials)

(defrule get-initial-under-chain=-when-has-initial-syntaxp
  (implies (and (has-initial x)
                (chain-elem-p y)
                (chain= x y)
                ;; Prevents looping
                (syntaxp (<< y x)))
           (equal (get-initial x)
                  (get-initial y)))
  :use get-initial-under-chain=-when-has-initial)

(defrule has-g-inverse-when-not-has-initial
  (implies (and (chain-elem-p x)
                (not (has-initial x))
                (polarity x))
           (has-g-inverse (chain-elem x)))
  :enable (initial-p)
  :use has-initial-when-initial-p-forward
  :rule-classes ((:forward-chaining :trigger-terms ((has-initial x)))))

(defrule has-f-inverse-when-not-has-initial
  (implies (and (chain-elem-p x)
                (not (has-initial x))
                (not (polarity x)))
           (has-f-inverse (chain-elem x)))
  :enable (initial-p)
  :use has-initial-when-initial-p-forward
  :rule-classes ((:forward-chaining :trigger-terms ((has-initial x)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; "Stoppers" are chains with initial elements. A p-stopper is a chain whose
;; initial element has positive polarity (is in p), and q-stopper is one whose
;; initial element has negative polarity (is in q).

(define in-q-stopper ((x chain-elem-p))
  (and (has-initial x)
       (not (polarity (get-initial x)))))

(defrule has-initial-when-in-q-stopper-forward
  (implies (in-q-stopper x)
           (has-initial x))
  :enable (in-q-stopper)
  :rule-classes :forward-chaining)

(defrule not-polarity-of-get-initial-when-in-q-stopper-forward
  (implies (in-q-stopper x)
           (not (polarity (get-initial x))))
  :enable (in-q-stopper)
  :rule-classes :forward-chaining)


(defrule has-g-inverse-when-in-q-stopper-forward
  (implies (and (in-q-stopper x)
                (polarity x))
           (has-g-inverse (chain-elem x)))
  :disable (has-g-inverse-of-chain-elem-when-chain<=)
  :use (:instance has-g-inverse-of-chain-elem-when-chain<=
                  (x (get-initial x))
                  (y x))
  :enable (in-q-stopper)
  :rule-classes ((:forward-chaining :trigger-terms ((in-q-stopper x)))))

(defruled has-f-inverse-when-not-in-q-stopper-forward
  (implies (and (chain-elem-p x)
                (not (in-q-stopper x))
                (not (polarity x)))
           (has-f-inverse (chain-elem x)))
  :enable (in-q-stopper)
  :disable (has-f-inverse-of-chain-elem-when-chain<=)
  :use ((:instance has-f-inverse-of-chain-elem-when-chain<=
                   (x (get-initial x))
                   (y x))
        (:instance has-f-inverse-when-not-has-initial)))


(defrule in-q-stopper-under-chain=
  (implies (chain= x y)
           (equal (in-q-stopper x)
                  (in-q-stopper y)))
  :enable (in-q-stopper)
  :rule-classes :congruence)
