(in-package "ACL2")
(include-book "basis")
(include-book "records")

#|

We define a cache-coherence memory-ordering protocol at a pretty high-level of
abstraction. This is loosely based on the MESI protocol.

The property we want to prove is the following:

Forall p,q,a,d: if (q completed the last write to address a with data d) and
                p reads address a and gets value d.

Well, it is easier to leave the specific q and d out of the equation and only
introduce p and a as skolem constants. We add appropriate auxiliary variables
to track this.

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;; definitions for example mesi cache system ;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate (((proc *) => *) ((op *) => *)
              ((addr *) => *) ((data *) => *))
 (local (defun proc (n) n)) (local (defun op (n) n))
 (local (defun addr (n) n)) (local (defun data (n) n)))

(encapsulate (((c-l *) => *)) (local (defun c-l (a) a)))

(define-system mesi-cache
 (mem (c n) nil
   (cond ((/= (c-l (addr n)) c) (mem c n-))
         ((and (= (op n) :flush)
               (in (proc n) (excl c n-)))
          (cache (proc n) c n-))
         (t (mem c n-))))

 (cache (p c n) nil
   (cond ((/= (c-l (addr n)) c) (cache p c n-))
         ((/= (proc n) p) (cache p c n-))
         ((or (and (= (op n) :fill) (not (excl c n-)))
              (and (= (op n) :fille) (not (valid c n-))))
          (mem c n-))
         ((and (= (op n) :store) (in p (excl c n-)))
          (s (addr n) (data n) (cache p c n-)))
         (t (cache p c n-))))

 (excl (c n) nil
   (cond ((/= (c-l (addr n)) c) (excl c n-))
         ((and (= (op n) :flush)
               (implies (excl c n-)
                        (in (proc n) (excl c n-))))
          (sdrop (proc n) (excl c n-)))
         ((and (= (op n) :fille) (not (valid c n-)))
          (sadd (proc n) (excl c n-)))
         (t (excl c n-))))

 (valid (c n) nil
   (cond ((/= (c-l (addr n)) c) (valid c n-))
         ((and (= (op n) :flush)
               (implies (excl c n-)
                        (in (proc n) (excl c n-))))
          (sdrop (proc n) (valid c n-)))
         ((or (and (= (op n) :fill) (not (excl c n-)))
              (and (= (op n) :fille) (not (valid c n-))))
          (sadd (proc n) (valid c n-)))
         (t (valid c n-)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;; definitions for mesi system specification ;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate (((p) => *) ((a) => *))
  (local (defun p () t)) (local (defun a () t))
  (defthm a-not-nil (equal (equal (a) nil) nil))
  (defthm p-not-nil (equal (equal (p) nil) nil)))

(define-system mesi-specification
 (a-dat (n) nil
   (if (and (equal (addr n) (a))
            (equal (op n) :store)
            (in (proc n) (excl (c-l (addr n)) n-)))
       (list (data n))
     (a-dat n-)))

 (ok (n) t
   (if (and (a-dat n-)
            (equal (proc n) (p))
            (equal (addr n) (a))
            (equal (op n) :load)
            (in (p) (valid (c-l (addr n)) n-)))
       (equal (g (a) (cache (p) (c-l (a)) n-))
              (car (a-dat n-)))
     (ok n-))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;; various auxiliary rules and definitions ;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; For the (proc n), (addr n), and (op n) inputs, we want to force
;; case-splits using the finite-cases macro from basis.lisp:

(finite-cases process-id :input (proc n) ((p) (scar (excl (c-l (a)) (t- n)))))
(finite-cases address    :input (addr n) ((a)))
(finite-cases operation  :input (op n)   (:store :fille :fill :flush :load))


;; We do want the following rewrite rule from the records book enabled:

(in-theory (enable g-of-s-redux))


;; The following function is only used as shorthand in provide a precise
;; case-split in rewrite rules below:

(defun <<s (e x) (implies x (<< e (scar x))))


;; These could probably be moved into the sets and records books, but it is
;; easy enough to include all of the if-lifting rules in one form:

(if-lift-rules
 (<<s x y)
 (car x)
 (cons x y)
 (g a r)
 (s a v r)
 (c1 r)
 (equal x y)
 (sdiff x y)
 (isect x y)
 (unite x y)
 (in e x)
 (subset x y)
 (scar a)
 (s1 a)
 (c-l a))


;; The following is an unfortunate rule that we need to add because the
;; rewriter does not handle equality reasoning across predicate
;; evaluations. This might be a worthwhile addition, but it could also be an
;; expensive proposition, so I need to continue working on this.

(defthm bogus-equality1
  (implies (not (equal (proc! a) (p)))
           (equal (equal (scar (excl (c-l (a)) n)) (proc! a))
                  (if (equal (scar (excl (c-l (a)) n)) (p)) nil
                    (hide (equal (scar (excl (c-l (a)) n)) (proc! a))))))
  :hints (("Goal" :expand (hide (equal (scar (excl (c-l (a)) n)) (proc! a))))))


;; The next set of rules are simply reorganized versions of rules from the sets
;; book which we need in order to introduce certain abstractions and/or force
;; certain case splits:

(defthm c1-of-sdrop-hide
  (equal (c1 (sdrop e x))
         (if (in e x) (if (c1 x) nil (hide (c1 (sdrop e x)))) (c1 x)))
  :hints (("Goal" :expand (hide (c1 (sdrop e x))))))

(defthm scar-of-sdrop-hide
  (equal (scar (sdrop e x))
         (if (in e x) (hide (scar (sdrop e x))) (scar x)))
  :hints (("Goal" :expand (hide (scar (sdrop e x))))))

(defthm scar-of-sadd
  (equal (scar (sadd e x))
         (if (<<s e x) e (scar x)))
  :hints (("Goal" :cases (x (not x)))))

(defthm drop-in-test-when-equal-scar
  (implies (and s (equal (scar s) e))
           (in e s)))

(defthm rename-of-wrap-up-s1
  (equal (equal s (s1 a))
         (and (c1 s) (equal (scar s) a))))


;; We will only use the following predicate in syntaxp tests below...

(defun st-predp (x)
  (declare (xargs :mode :program))
  (not (intersectp-eq '(t+ hide) (all-fnnames x))))


;; Ok, the key insight to this invariant proof is to case-split the test of a
;; node in an :excl set by testing if the :excl set is empty, a singleton of
;; the last guy to be added to the :excl set, or abstracted (we don't care
;; because we don't expect this case to ever occur -- or at least not
;; matter). We need the syntaxp test to make sure we only apply this in cases
;; where we are trying to case-split out a selected input, but also we must
;; ensure that the resulting tests and cases will in fact be rep terms.

(defthm in-excl-rdx
  (implies (syntaxp (not (st-predp e)))
           (equal (in e (excl c n))
                  (cond ((not (excl c n)) nil)
                        ((c1 (excl c n)) (equal e (scar (excl c n))))
                        (t (hide (in e (excl c n)))))))
  :hints (("Goal" :expand (hide (in e (excl c n))))))


;; And now we abstract the terms which we do not wish to include in state
;; information for the MESI model:

(abstract-terms (in 'nil (excl (c-l (a)) n))
                (equal (scar (excl (c-l (a)) n)) 'nil)
                (equal (g (a) (cache 'nil (c-l (a)) n)) (car (a-dat n)))
                (equal (scar (valid c n)) e)
                (c1 (valid c n)))


;; This final theorem basically defines the only case of <<s we care about:

(defthm <<s-of-nil
  (equal (<<s e x) (if x (hide (<<s e x)) t))
  :hints (("Goal" :expand (hide (<<s e x)))))

(in-theory (disable <<s))

