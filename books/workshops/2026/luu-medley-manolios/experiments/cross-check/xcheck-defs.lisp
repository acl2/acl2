; xcheck-defs.lisp -- cross-validation scaffold: OUR connectivity chain
; (../main, ../standard) side by side with THEIR chain (x-connectivity, the
; mechanically renamed ALENEX formalization; see rename.py), translations
; between the two representations, deterministic pseudo-random correct
; schemes, and the executable properties tested by xcheck-tests.lsp with
; cgen.  The assert-events at the end exercise the main cross-check (c) on
; fixed seeds during certification.
;
; Representations.
;   OURS:   n x n matrix = list of n rows of n bits; summand (A B C);
;           scheme = obag of summands; move (:flip p s1 s2) / (:plus p target pivot).
;   THEIRS: matrix = flat bit list of length n*n, entry (i,j) at i*n+j
;           (= our mat-flat); summand (A B C) of flat vectors; scheme = list
;           read up to perm; move (:flip p s u) / (:plus p piv tgt);
;           apply-move takes L = n*n first.
;
; Guard note: the properties call THEIR functions, most of which are
; :verify-guards nil, through ec-call, so every function in this book is
; guard-verified.

(in-package "ACL2")

(include-book "../../main")
(include-book "../../standard")
(include-book "x-connectivity")
(include-book "arithmetic-5/top" :dir :system)

;; ---- pseudo-random generator (LCG, glibc constants, 31-bit state) ----
(define lcg-next ((x natp))
  :returns (y natp :hyp :guard)
  (mod (+ (* 1103515245 x) 12345) 2147483648))
(define lcg-pick ((x natp) (k posp))
  :returns (i natp)
  (if (zp k) 0 (mod (floor (nfix x) 65536) k))
  ///
  (defrule lcg-pick-bound
    (implies (posp k)
             (< (lcg-pick x k) k))
    :rule-classes :linear))

(defruled len-equal-0
  (equal (equal (len x) 0) (atom x)))

(defruled len-when-consp
  (implies (consp x) (< 0 (len x)))
  :rule-classes :linear)

(defruled true-listp-when-move-list-p
  (implies (move-list-p l) (true-listp l)))

(define rand-bits ((k natp) (x natp))
  :returns (mv (bits bit-list-p) (x1 natp :hyp (natp x)))
  :verify-guards :after-returns
  (if (zp k)
      (mv nil (lnfix x))
    (b* ((x (lcg-next x))
         ((mv rest x) (rand-bits (1- k) x)))
      (mv (cons (if (eql (lcg-pick x 2) 0) 0 1) rest) x))))

(define rand-mat ((m natp) (n natp) (x natp))
  :returns (mv (a bit-list-listp) (x1 natp :hyp (natp x)))
  :verify-guards :after-returns
  (if (zp m)
      (mv nil (lnfix x))
    (b* (((mv row x) (rand-bits n x))
         ((mv rest x) (rand-mat (1- m) n x)))
      (mv (cons row rest) x))))

(define rand-triple ((n natp) (x natp))
  :returns (mv (s mat-triplep) (x1 natp :hyp (natp x)))
  :verify-guards :after-returns
  (b* (((mv a x) (rand-mat n n x))
       ((mv b x) (rand-mat n n x))
       ((mv c x) (rand-mat n n x)))
    (mv (list a b c) x)))

(define rand-triple-list ((k natp) (n natp) (x natp))
  :returns (mv (l mat-triple-listp) (x1 natp :hyp (natp x)))
  :verify-guards :after-returns
  (if (zp k)
      (mv nil (lnfix x))
    (b* (((mv s x) (rand-triple n x))
         ((mv rest x) (rand-triple-list (1- k) n x)))
      (mv (cons s rest) x))))

;; random list of 0..6 triples (mostly NOT a correct scheme)
(define rand-triples ((seed natp) (n natp))
  :returns (l mat-triple-listp)
  (b* ((x (lcg-next seed))
       (k (lcg-pick x 7))
       ((mv l &) (rand-triple-list k n (lcg-next x))))
    l))

;; ---- all valid moves of a scheme ----

(define moves-filter ((cands move-list-p) (sch obag::bagp))
  :returns (l move-list-p :hyp :guard)
  (cond ((atom cands) nil)
        ((move-validp (car cands) sch)
         (cons (car cands) (moves-filter (cdr cands) sch)))
        (t (moves-filter (cdr cands) sch))))

(define moves-for-pair ((s1 mat-triplep) (s2 mat-triplep) (sch obag::bagp))
  :returns (l move-list-p :hyp :guard)
  (moves-filter (list (list :flip 0 s1 s2) (list :flip 1 s1 s2) (list :flip 2 s1 s2)
                      (list :plus 0 s1 s2) (list :plus 1 s1 s2) (list :plus 2 s1 s2))
                sch))

(define moves-for-s1 ((s1 mat-triplep) (others mat-triple-listp) (sch obag::bagp))
  :returns (l move-list-p :hyp :guard)
  (if (atom others)
      nil
    (append (moves-for-pair s1 (car others) sch)
            (moves-for-s1 s1 (cdr others) sch))))

(define all-moves-aux ((l mat-triple-listp) (sch obag::bagp))
  :guard (mat-triple-listp sch)
  :guard-hints (("Goal" :in-theory (enable mat-triple-listp-of-remove1-equal)))
  :returns (moves move-list-p :hyp :guard
                  :hints (("Goal" :in-theory (enable mat-triple-listp-of-remove1-equal))))
  (if (atom l)
      nil
    (append (moves-for-s1 (car l) (remove1-equal (car l) sch) sch)
            (all-moves-aux (cdr l) sch))))

(define all-moves ((sch obag::bagp))
  :guard (mat-triple-listp sch)
  :returns (moves move-list-p :hyp :guard)
  (all-moves-aux sch sch))

(define flips-only ((moves move-list-p))
  :returns (l move-list-p :hyp :guard)
  (cond ((atom moves) nil)
        ((eq (move-kind (car moves)) :flip)
         (cons (car moves) (flips-only (cdr moves))))
        (t (flips-only (cdr moves)))))

(defrule move-p-of-nth-when-move-list-p
  (implies (and (move-list-p l) (natp i) (< i (len l)))
           (move-p (nth i l))))

(defrule move-p-of-nth-lcg-pick
  (implies (and (move-list-p l) (consp l))
           (move-p (nth (lcg-pick x (len l)) l)))
  :use ((:instance lcg-pick-bound (k (len l)))
        (:instance move-p-of-nth-when-move-list-p (i (lcg-pick x (len l)))))
  :enable (len-when-consp true-listp-when-move-list-p)
  :disable (lcg-pick-bound move-p-of-nth-when-move-list-p))

(defrule mat-triple-listp-of-apply-move
  (implies (and (mat-triple-listp sch) (obag::bagp sch) (move-p move))
           (mat-triple-listp (apply-move move sch n)))
  :enable (apply-move mat-triple-listp-of-insert mat-triple-listp-of-delete))

;; the moves the walk may take: above the rank cap only flips
(define walk-moves ((sch obag::bagp) (cap natp))
  :guard (mat-triple-listp sch)
  :returns (moves move-list-p :hyp :guard)
  (b* ((moves (all-moves sch)))
    (if (<= cap (len sch)) (flips-only moves) moves)))

;; random walk of k valid moves
(define rand-walk ((k natp) (sch obag::bagp) (n natp) (cap natp) (x natp))
  :guard (mat-triple-listp sch)
  :returns (sch1 obag::bagp :hyp (obag::bagp sch))
  :guard-hints (("Goal" :do-not-induct t
                 :use ((:instance move-p-of-nth-lcg-pick
                                  (l (walk-moves sch cap)) (x (lcg-next x))))
                 :in-theory (e/d (len-equal-0 len-when-consp true-listp-when-move-list-p)
                                 (nth len move-p move-p-of-nth-lcg-pick))))
  (if (zp k)
      sch
    (b* ((moves (walk-moves sch cap))
         ((when (atom moves)) sch)
         (x (lcg-next x))
         (i (lcg-pick x (len moves)))
         (m (nth i moves)))
      (rand-walk (1- k) (apply-move m sch n) n cap (lcg-next x)))))

(define rand-scheme ((seed natp) (n natp))
  :returns (sch obag::bagp)
  :guard-hints (("Goal" :in-theory (enable standard-scheme)))
  (b* ((x (lcg-next seed))
       (k (+ 1 (lcg-pick x 10))))
    (rand-walk k (standard-scheme n) n (+ 6 (* n n n)) (lcg-next x))))

(define rand-move ((seed natp) (sch obag::bagp))
  :guard (mat-triple-listp sch)
  :returns (m (or (null m) (move-p m)) :hyp :guard
              :hints (("Goal" :do-not-induct t
                       :use ((:instance move-p-of-nth-lcg-pick
                                        (l (all-moves sch)) (x (lcg-next seed))))
                       :in-theory (e/d (len-equal-0 len-when-consp true-listp-when-move-list-p)
                                       (nth len move-p move-p-of-nth-lcg-pick)))))
  :guard-hints (("Goal" :do-not-induct t
                 :in-theory (e/d (len-equal-0 len-when-consp true-listp-when-move-list-p)
                                 (nth len move-p))))
  (b* ((moves (all-moves sch))
       ((when (atom moves)) nil)
       (i (lcg-pick (lcg-next seed) (len moves))))
    (nth i moves)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Translations between the two representations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; matrices: rows -> flat vector (their bvp of length n*n)
(define to-x-mat ((a bit-list-listp))
  :returns (v bit-list-p :hyp :guard)
  (mat-flat a))

(define take-bits ((k natp) (v bit-list-p))
  :returns (r bit-list-p)
  (if (zp k)
      nil
    (cons (if (eql (car v) 1) 1 0) (take-bits (1- k) (cdr v)))))

(define drop-bits ((k natp) (v bit-list-p))
  :returns (r bit-list-p :hyp :guard)
  (if (zp k)
      v
    (drop-bits (1- k) (cdr v))))

(define from-x-mat-rows ((v bit-list-p) (m natp) (n natp))
  :returns (a bit-list-listp)
  (if (zp m)
      nil
    (cons (take-bits n v) (from-x-mat-rows (drop-bits n v) (1- m) n))))

;; flat vector of length n*n -> n rows of n bits
(define from-x-mat ((v bit-list-p) (n natp))
  :returns (a bit-list-listp)
  (from-x-mat-rows v n n))

;; shape of THEIR summands / schemes / moves (dimension-free)
(define xsummand-shapep (s)
  :returns (yes/no booleanp)
  (and (true-listp s)
       (equal (len s) 3)
       (bit-list-p (car s))
       (bit-list-p (cadr s))
       (bit-list-p (caddr s))))

(define xscheme-shapep (l)
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (xsummand-shapep (car l))
         (xscheme-shapep (cdr l)))))

(define to-x-summand ((s mat-triplep))
  :returns (xs xsummand-shapep :hyp :guard :hints (("Goal" :in-theory (enable xsummand-shapep))))
  (list (to-x-mat (car s)) (to-x-mat (cadr s)) (to-x-mat (caddr s))))

(define from-x-summand ((s xsummand-shapep) (n natp))
  :returns (r mat-triplep)
  :guard-hints (("Goal" :in-theory (enable xsummand-shapep)))
  (list (from-x-mat (car s) n) (from-x-mat (cadr s) n) (from-x-mat (caddr s) n)))

;; the matrix and summand translations are mutually inverse on well-formed
;; (n x n) data
(defrule take-bits-of-append
  (implies (bit-listnp x n)
           (equal (take-bits n (append x y)) x))
  :induct (bit-listnp x n)
  :enable (take-bits bit-listnp))

(defrule drop-bits-of-append
  (implies (bit-listnp x n)
           (equal (drop-bits n (append x y)) y))
  :induct (bit-listnp x n)
  :enable (drop-bits bit-listnp))

(defrule from-x-mat-rows-of-mat-flat
  (implies (and (bit-matp a m n) (natp m) (natp n))
           (equal (from-x-mat-rows (mat-flat a) m n) a))
  :induct (bit-matp a m n)
  :enable (from-x-mat-rows mat-flat bit-matp))

(defrule from-x-mat-of-to-x-mat
  (implies (and (bit-matp a n n) (natp n))
           (equal (from-x-mat (to-x-mat a) n) a))
  :enable (from-x-mat to-x-mat))

(defrule from-x-summand-of-to-x-summand
  (implies (and (summand-dimp s n) (natp n))
           (equal (from-x-summand (to-x-summand s) n) s))
  :enable (from-x-summand to-x-summand))

;; schemes: obag -> list (any order; theirs is read up to perm)
(define to-x-scheme ((sch mat-triple-listp))
  :returns (l xscheme-shapep :hyp :guard :hints (("Goal" :in-theory (enable xscheme-shapep))))
  (if (atom sch)
      nil
    (cons (to-x-summand (car sch)) (to-x-scheme (cdr sch)))))

;; list -> obag, by insertion
(define from-x-scheme ((l xscheme-shapep) (n natp))
  :returns (sch obag::bagp)
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable xscheme-shapep)))
  (if (atom l)
      nil
    (obag::insert (from-x-summand (car l) n) (from-x-scheme (cdr l) n))))

(define xmove-shapep (m)
  :returns (yes/no booleanp)
  (and (true-listp m)
       (equal (len m) 4)
       (or (eq (car m) :flip) (eq (car m) :plus))
       (natp (cadr m))
       (< (cadr m) 3)
       (xsummand-shapep (caddr m))
       (xsummand-shapep (cadddr m))))

;; moves.  Positions agree (0 1 2 = A B C).
;;   plus: ours (:plus p target pivot), theirs (:plus p piv tgt): reversed.
;;   flip: ours (:flip p s1 s2) gives s1 its pos-prev(p) factor summed and s2
;;         its pos-next(p) factor summed; theirs (:flip p s u) gives s the
;;         HIGHER and u the LOWER of the two other positions.  These coincide
;;         for p = 0 (prev 2, next 1) and p = 2 (prev 1, next 0) but for p = 1
;;         ours is (s1: A, s2: C) and theirs (s: C, u: A), so the two
;;         summands are swapped at p = 1.
(define to-x-move ((m move-p))
  :returns (xm xmove-shapep :hyp :guard :hints (("Goal" :in-theory (enable xmove-shapep))))
  (b* ((p (move-pos m))
       (s1 (to-x-summand (move-s1 m)))
       (s2 (to-x-summand (move-s2 m))))
    (case (move-kind m)
      (:flip (if (eql p 1) (list :flip p s2 s1) (list :flip p s1 s2)))
      (t (list :plus p s2 s1)))))

;; the "obvious" translation that ignores the flip convention (used only to
;; exhibit the p = 1 discrepancy)
(define to-x-move-naive ((m move-p))
  :returns (xm xmove-shapep :hyp :guard :hints (("Goal" :in-theory (enable xmove-shapep))))
  (b* ((p (move-pos m))
       (s1 (to-x-summand (move-s1 m)))
       (s2 (to-x-summand (move-s2 m))))
    (case (move-kind m)
      (:flip (list :flip p s1 s2))
      (t (list :plus p s2 s1)))))

(define from-x-move ((m xmove-shapep) (n natp))
  :returns (r move-p :hyp :guard
              :hints (("Goal" :in-theory (e/d (xmove-shapep) (mat-triplep)))))
  :guard-hints (("Goal" :in-theory (enable xmove-shapep)))
  (b* ((p (cadr m))
       (a (from-x-summand (caddr m) n))
       (b (from-x-summand (cadddr m) n)))
    (case (car m)
      (:flip (if (eql p 1) (list :flip p b a) (list :flip p a b)))
      (t (list :plus p b a)))))

(define xpath-shapep (l)
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (xmove-shapep (car l))
         (xpath-shapep (cdr l)))))

(define to-x-path ((moves move-list-p))
  :returns (l xpath-shapep :hyp :guard :hints (("Goal" :in-theory (enable xpath-shapep))))
  (if (atom moves)
      nil
    (cons (to-x-move (car moves)) (to-x-path (cdr moves)))))

(define from-x-path ((l xpath-shapep) (n natp))
  :returns (moves move-list-p :hyp :guard
                  :hints (("Goal" :in-theory (enable xpath-shapep))))
  :guard-hints (("Goal" :in-theory (enable xpath-shapep)))
  (if (atom l)
      nil
    (cons (from-x-move (car l) n) (from-x-path (cdr l) n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Random perturbations of a correct scheme (for the negative cases of (a))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule mat-triplep-of-nth-when-mat-triple-listp
  (implies (and (mat-triple-listp l) (natp i) (< i (len l)))
           (mat-triplep (nth i l))))

(defrule mat-triplep-of-nth-lcg-pick
  (implies (and (mat-triple-listp l) (consp l))
           (mat-triplep (nth (lcg-pick x (len l)) l)))
  :use ((:instance lcg-pick-bound (k (len l)))
        (:instance mat-triplep-of-nth-when-mat-triple-listp (i (lcg-pick x (len l)))))
  :enable (len-when-consp true-listp-when-mat-triple-listp)
  :disable (lcg-pick-bound mat-triplep-of-nth-when-mat-triple-listp))

;; mode 0: unchanged; 1: delete a summand; 2: duplicate a summand;
;; 3: insert a random triple (possibly with a zero factor)
(define perturb ((seed natp) (sch obag::bagp) (n natp))
  :guard (mat-triple-listp sch)
  :returns (sch1 obag::bagp :hyp (obag::bagp sch))
  :guard-hints (("Goal" :do-not-induct t
                 :in-theory (e/d (len-equal-0 len-when-consp
                                  true-listp-when-mat-triple-listp)
                                 (nth len mat-triplep))))
  (b* ((x (lcg-next seed))
       (mode (lcg-pick x 4))
       ((when (or (eql mode 0) (atom sch))) sch)
       ((when (eql mode 3))
        (b* (((mv s &) (rand-triple n (lcg-next x))))
          (obag::insert s sch)))
       (s (nth (lcg-pick (lcg-next x) (len sch)) sch)))
    (if (eql mode 1)
        (obag::delete s sch)
      (obag::insert s sch))))

;; a random candidate move on THEIR side: kind, position and two summands
;; drawn (independently, possibly the same) from the list; nil if empty
(define rand-x-move ((seed natp) (xs xscheme-shapep))
  :returns (xm (or (null xm) (xmove-shapep xm)) :hyp :guard
               :hints (("Goal" :do-not-induct t
                        :in-theory (e/d (xmove-shapep len-equal-0 len-when-consp
                                         xsummand-shapep-of-nth-lcg-pick
                                         true-listp-when-xscheme-shapep)
                                        (nth len)))))
  :guard-hints (("Goal" :do-not-induct t
                 :in-theory (e/d (len-equal-0 len-when-consp
                                  true-listp-when-xscheme-shapep)
                                 (nth len))))
  :prepwork
  ((defruled true-listp-when-xscheme-shapep
     (implies (xscheme-shapep l) (true-listp l))
     :enable xscheme-shapep)
   (defrule xsummand-shapep-of-nth-when-xscheme-shapep
     (implies (and (xscheme-shapep l) (natp i) (< i (len l)))
              (xsummand-shapep (nth i l)))
     :enable xscheme-shapep)
   (defruled xsummand-shapep-of-nth-lcg-pick
     (implies (and (xscheme-shapep l) (consp l))
              (xsummand-shapep (nth (lcg-pick x (len l)) l)))
     :use ((:instance lcg-pick-bound (k (len l)))
           (:instance xsummand-shapep-of-nth-when-xscheme-shapep (i (lcg-pick x (len l)))))
     :enable (len-when-consp true-listp-when-xscheme-shapep)
     :disable (lcg-pick-bound xsummand-shapep-of-nth-when-xscheme-shapep)))
  (b* (((when (atom xs)) nil)
       (x (lcg-next seed))
       (kind (if (eql (lcg-pick x 2) 0) :flip :plus))
       (x (lcg-next x))
       (p (lcg-pick x 3))
       (x (lcg-next x))
       (i (lcg-pick x (len xs)))
       (x (lcg-next x))
       (j (lcg-pick x (len xs))))
    (list kind p (nth i xs) (nth j xs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The properties (executable predicates; THEIR functions via ec-call)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule move-p-of-walk-pick
  (implies (and (mat-triple-listp sch) (obag::bagp sch) (natp cap)
                (consp (walk-moves sch cap)))
           (move-p (nth (lcg-pick x (len (walk-moves sch cap)))
                        (walk-moves sch cap))))
  :disable (move-p))

(defrule mat-triple-listp-of-rand-walk
  (implies (and (mat-triple-listp sch) (obag::bagp sch) (natp cap))
           (mat-triple-listp (rand-walk k sch n cap x)))
  :induct (rand-walk k sch n cap x)
  :enable (rand-walk)
  :disable (move-p move-p-of-nth-lcg-pick))

(defrule mat-triple-listp-of-rand-scheme
  (implies (natp n)
           (mat-triple-listp (rand-scheme seed n)))
  :enable (rand-scheme standard-scheme))

;; the perturbations keep the shape
(defrule mat-triple-listp-of-perturb
  (implies (and (mat-triple-listp sch) (obag::bagp sch))
           (mat-triple-listp (perturb seed sch n)))
  :enable (perturb mat-triple-listp-of-insert mat-triple-listp-of-delete)
  :disable (mat-triplep nth len))

;; (a) correct-schemep agrees with x-schemep under translation
(define prop-a ((sch obag::bagp) (n natp))
  :guard (mat-triple-listp sch)
  :returns (yes/no booleanp)
  (iff (correct-schemep sch n)
       (ec-call (x-schemep n (to-x-scheme sch)))))

(define prop-a-triples ((seed natp) (n natp))
  :returns (yes/no booleanp)
  (prop-a (insert-list (rand-triples seed n) nil) n))

(define prop-a-rand ((seed natp) (n natp))
  :returns (yes/no booleanp)
  (prop-a (rand-scheme seed n) n))

(define prop-a-perturbed ((seed natp) (n natp))
  :returns (yes/no booleanp)
  (prop-a (perturb (lcg-next seed) (rand-scheme seed n) n) n))

;; (b) a random valid move of ours is valid for them and the results agree
;;     (up to perm) -- with the correct translation ...
(define prop-b ((seed natp) (n natp))
  :returns (yes/no booleanp)
  :guard-hints (("Goal" :do-not-induct t
                 :use ((:instance return-type-of-rand-move
                                  (seed (lcg-next seed)) (sch (rand-scheme seed n))))
                 :in-theory (disable move-p return-type-of-rand-move)))
  (b* ((sch (rand-scheme seed n))
       (m (rand-move (lcg-next seed) sch))
       ((unless m) t)
       (xs (to-x-scheme sch))
       (xm (to-x-move m))
       (L (* n n)))
    (and (move-validp m sch)
         (ec-call (x-move-ok-p xm xs))
         (ec-call (perm (ec-call (x-apply-move L xm xs))
                        (to-x-scheme (apply-move m sch n)))))))

;; ... and with the naive translation (expected to FAIL on p = 1 flips)
(define prop-b-naive ((seed natp) (n natp))
  :returns (yes/no booleanp)
  :guard-hints (("Goal" :do-not-induct t
                 :use ((:instance return-type-of-rand-move
                                  (seed (lcg-next seed)) (sch (rand-scheme seed n))))
                 :in-theory (disable move-p return-type-of-rand-move)))
  (b* ((sch (rand-scheme seed n))
       (m (rand-move (lcg-next seed) sch))
       ((unless m) t)
       (xs (to-x-scheme sch))
       (xm (to-x-move-naive m))
       (L (* n n)))
    (and (move-validp m sch)
         (ec-call (x-move-ok-p xm xs))
         (ec-call (perm (ec-call (x-apply-move L xm xs))
                        (to-x-scheme (apply-move m sch n)))))))

;; (b') a random candidate move on THEIR side: validity agrees, and when
;;      valid the results agree (their result translated back = ours)
(define prop-b-conv ((seed natp) (n natp))
  :returns (yes/no booleanp)
  :guard-hints (("Goal" :do-not-induct t
                 :use ((:instance return-type-of-rand-x-move
                                  (seed (lcg-next seed))
                                  (xs (to-x-scheme (rand-scheme seed n)))))
                 :in-theory (disable move-p xmove-shapep return-type-of-rand-x-move)))
  (b* ((sch (rand-scheme seed n))
       (xs (to-x-scheme sch))
       (xm (rand-x-move (lcg-next seed) xs))
       ((unless xm) t)
       (m (from-x-move xm n))
       (ok1 (ec-call (x-move-ok-p xm xs)))
       (ok2 (move-validp m sch)))
    (and (iff ok1 ok2)
         (or (not ok1)
             (b* ((xres (ec-call (x-apply-move (* n n) xm xs)))
                  ((unless (xscheme-shapep xres)) nil))
               (equal (apply-move m sch n) (from-x-scheme xres n)))))))

;; round trips of the translations on random data
(define prop-roundtrip ((seed natp) (n natp))
  :returns (yes/no booleanp)
  :guard-hints (("Goal" :do-not-induct t
                 :use ((:instance return-type-of-rand-move
                                  (seed (lcg-next seed)) (sch (rand-scheme seed n))))
                 :in-theory (disable move-p return-type-of-rand-move)))
  (b* ((sch (rand-scheme seed n))
       (m (rand-move (lcg-next seed) sch)))
    (and (equal (from-x-scheme (to-x-scheme sch) n) sch)
         (or (not m)
             (equal (from-x-move (to-x-move m) n) m)))))

;; (c) THE MAIN CROSS-CHECK: our main-path, checked by their definitions
(define prop-c ((s1 natp) (s2 natp) (n natp))
  :returns (yes/no booleanp)
  (b* ((sch (rand-scheme s1 n))
       (sch2 (rand-scheme s2 n))
       (L (* n n))
       (path (main-path sch sch2 n))
       (xpath (to-x-path path))
       (xs (to-x-scheme sch))
       (xs2 (to-x-scheme sch2)))
    (and (ec-call (x-path-ok-p L xpath xs))
         (ec-call (perm (ec-call (x-apply-path L xpath xs)) xs2)))))

;; (c') their connect-path, checked by our definitions
(define prop-c-conv ((s1 natp) (s2 natp) (n natp))
  :returns (yes/no booleanp)
  (b* ((sch (rand-scheme s1 n))
       (sch2 (rand-scheme s2 n))
       (xs (to-x-scheme sch))
       (xs2 (to-x-scheme sch2))
       (xpath (ec-call (x-connect-path n xs xs2)))
       ((unless (xpath-shapep xpath)) nil)
       (path (from-x-path xpath n)))
    (and (path-validp path sch n)
         (equal (apply-moves path sch n) sch2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Guard-t wrappers for cgen.  cgen evaluates conjectures with guard
;;; checking :none, under which guard-verified functions with a non-trivial
;;; guard run interpretively through their *1* functions (200x slower at
;;; n = 3: 8 s per prop-a-rand, 18 s per prop-c); a guard-verified function
;;; whose guard is t is entered in raw Lisp directly, so these wrappers make
;;; the tests run at compiled speed.  Non-natural inputs are vacuously true.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro def-prop-t (name fn args)
  `(define ,name ,args
     :guard t
     :returns (yes/no booleanp)
     (if (and ,@(pairlis$ (make-list (len args) :initial-element 'natp)
                          (pairlis$ args nil)))
         (,fn ,@args)
       t)))

(def-prop-t prop-a-triples-t prop-a-triples (seed n))
(def-prop-t prop-a-rand-t prop-a-rand (seed n))
(def-prop-t prop-a-perturbed-t prop-a-perturbed (seed n))
(def-prop-t prop-b-t prop-b (seed n))
(def-prop-t prop-b-naive-t prop-b-naive (seed n))
(def-prop-t prop-b-conv-t prop-b-conv (seed n))
(def-prop-t prop-roundtrip-t prop-roundtrip (seed n))
(def-prop-t prop-c-t prop-c (s1 s2 n))
(def-prop-t prop-c-conv-t prop-c-conv (s1 s2 n))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Deterministic instances of the main cross-check, run at certification
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (and (prop-a-rand 0 2) (prop-a-rand 1 2) (prop-a-triples 0 2) (prop-a-triples 1 2)))
(assert-event (and (prop-b 0 2) (prop-b 1 2) (prop-b 2 2) (prop-b 3 2)))
(assert-event (and (prop-b-conv 0 2) (prop-b-conv 1 2) (prop-b-conv 2 2) (prop-b-conv 3 2)))
(assert-event (and (prop-c 0 1 2) (prop-c 1 0 2) (prop-c 2 3 2) (prop-c 3 2 2) (prop-c 4 4 2)))
(assert-event (and (prop-c-conv 0 1 2) (prop-c-conv 1 0 2) (prop-c-conv 2 3 2) (prop-c-conv 3 2 2)
                   (prop-c-conv 4 4 2)))
(assert-event (and (prop-c 0 1 3) (prop-c-conv 0 1 3)))
