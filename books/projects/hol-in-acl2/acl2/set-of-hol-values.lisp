; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

; This book defines a set, V_{omega*2} -- the result of iterating powerset
; omega*2 times -- and proves that all HOL values are in this set.

; As of this writing, we don't need this book because the HOL props generated
; by translating theories implicitly create HOL values as sets.  But down the
; road there could be a need to have a "bounding set" on which to use
; separation to show that a given HOL value is a set, and this book's final
; theorem provides that set as (v-omega*2).

; FIrst we define the cumulative hierarchy for omega steps beyond V_{omega}.
; At some point we may implement ordinal recursion to define V_{alpha} for all
; ordinals alpha, but for now we only go up to V_{omega*2}.

(include-book "hol")

(defun v-omega+-n (n)
  (declare (type (integer 0 *) n))
  (if (zp n)
      (v-omega)
    (powerset (v-omega+-n (1- n)))))

(zfn v-omega+ () x y (omega)
     (equal (equal y (v-omega+-n x)) t))

(defthmz domain-v-omega+
  (equal (domain (v-omega+))
         (omega))
  :props (zfc v-omega+$prop domain$prop)
  :hints (("Goal"
           :expand ((subset (omega) (domain (v-omega+))))
           :in-theory (enable extensionality-rewrite)
           :restrict ((v-omega+$domain-2
                       ((y (v-omega+-n (subset-witness
                                        (omega)
                                        (domain (v-omega+)))))))))))

(defun v-omega*2 ()
  (declare (xargs :guard t))
  (union (image (v-omega+))))

(defthmz transitive-v-omega+-n
  (implies (natp n)
           (transitive (v-omega+-n n)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop))

(defthmz subset-vn-omega+n-v-omega*2
  (implies (force (natp m))
           (subset (v-omega+-n m) (v-omega*2)))
  :props (zfc v-omega+$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal"
           :in-theory (e/d (apply-intro) (equal-apply))
           :restrict ((in-image-suff ((p (cons m (v-omega+-n m)))))))))

(defthmz subset-v-omega-v-omega*2
  (subset (v-omega) (v-omega*2))
  :props (zfc v-omega+$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal"
           :in-theory (disable subset-vn-omega+n-v-omega*2)
           :use ((:instance subset-vn-omega+n-v-omega*2 (m 0)))))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable v-omega*2 (:e v-omega*2)))

(defthmz symbolp-implies-in-v-omega*2
  (implies (symbolp x)
           (in x (v-omega*2)))
  :props (zfc v$prop v-omega+$prop domain$prop prod2$prop inverse$prop))
  
; A handy abbreviation, defined so that it's clearly a natural number:
(defun v-omega+-n-inv (x)
  (let* ((sx (in-in-witness x (image (v-omega+))))
         (nx (apply (inverse (v-omega+)) sx)))
    (nfix nx)))

(defthmz in-v-omega*2-implies-in-v-omega+-n-lemma
  (implies (in x (v-omega*2))
           (let* ((sx (in-in-witness x (image (v-omega+))))
                  (nx (apply (inverse (v-omega+)) sx)))
             (in (cons nx sx) (v-omega+))))
  :props (zfc domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (enable in-in v-omega*2)))
  :rule-classes nil)

(defthmz in-v-omega+-implies-natp-car-1
  (implies (in (cons n obj) (v-omega+))
           (natp n))
  :props (zfc v-omega+$prop domain$prop)
  :hints (("Goal" :in-theory (e/d (apply-intro)
                                  (equal-apply v-omega+$domain-1))))
  :rule-classes :forward-chaining)

(defthmd apply-intro-non-empty-fun
  (implies (and (syntaxp (not (and (quotep f)
                                   (equal (unquote f) 0))))
                (funp f)
                (force? (zfc))
                (force? (domain$prop)))
           (equal (in p f)
                  (and (consp p)
                       (in (car p) (domain f))
                       (equal (cdr p) (apply f (car p))))))
  :hints (("Goal" :by apply-intro)))

(defthmz in-v-omega+-implies-natp-car-2
  (implies (in p (v-omega+))
           (and (consp p)
                (natp (car p))))
  :props (zfc v-omega+$prop domain$prop)
  :hints (("Goal" :in-theory (e/d (apply-intro-non-empty-fun)
                                  (equal-apply v-omega+$domain-1))))
  :rule-classes :forward-chaining)

(defthmz in-v-omega*2-implies-in-v-omega+-n-lemma-corollary
  (implies (in x (v-omega*2))
           (let* ((sx (in-in-witness x (image (v-omega+))))
                  (nx (apply (inverse (v-omega+)) sx)))
             (and (equal sx (v-omega+-n nx))
                  (in nx (omega)))))
  :props (zfc v-omega+$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (enable in-in v-omega*2)))
  :rule-classes nil)

(defthmz in-v-omega+-implies-in-v-omega+-n
  (implies (in x (v-omega*2))
           (in x (v-omega+-n (v-omega+-n-inv x))))
  :props (zfc v-omega+$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :use in-v-omega*2-implies-in-v-omega+-n-lemma-corollary
           :in-theory (enable in-in v-omega*2)))
  :rule-classes (:rewrite :forward-chaining))

; Start proof of relation-in-v-omega*2.

(defthmz v-omega+-n-monotone
  (implies (and (natp i)
                (natp j)
                (<= i j))
           (subset (v-omega+-n i) (v-omega+-n j)))
  :props (zfc v$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal" :induct (v-omega+-n j))))

(in-theory (disable v-omega+-n-inv))

(defthmz relation-in-v-omega*2-lemma-1
  (implies (and (relation-p x)
                (in (domain x) (v-omega*2))
                (in (image x) (v-omega*2)))
           (subset x (prod2
                       (v-omega+-n (v-omega+-n-inv (domain x)))
                       (v-omega+-n (v-omega+-n-inv (image x))))))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc v-omega+$prop inverse$prop prod2$prop domain$prop v$prop))

(defthmz relation-in-v-omega*2-lemma-2
  (implies (and (natp i)
                (natp j)
                (subset x (prod2 (v-omega+-n i) (v-omega+-n j))))
; Then x is a set of ordered pairs <a,b> = {{a},{a,b}} where a and b are in the
; respective v's.  Let k = 3 + max(i,j).  Both {a} and {a,b} are in
; v_{omega+k-2}, so <a,b> \in v_{omega+k-1}.  So x is in v_{omega+k}.
           (in x (v-omega+-n (+ 3 (max i j)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable subset-prod2-powerset-powerset)
           :use ((:instance subset-prod2-powerset-powerset
                            (dom (v-omega+-n i))
                            (ran (v-omega+-n j))
                            (s (v-omega+-n (max i j)))))
           :expand ((v-omega+-n (+ 3 i))
                    (v-omega+-n (+ 2 i))
                    (v-omega+-n (+ 3 j))
                    (v-omega+-n (+ 2 j)))))
  :otf-flg t
  :props (zfc v-omega+$prop inverse$prop prod2$prop domain$prop v$prop)
  :rule-classes nil)

(defthmz relation-in-v-omega*2
  (implies (and (relation-p x)
                (in (domain x) (v-omega*2))
                (in (image x) (v-omega*2)))
           (in x (v-omega*2)))
  :hints (("Goal"
           :use ((:instance relation-in-v-omega*2-lemma-2
                            (i (v-omega+-n-inv (domain x)))
                            (j (v-omega+-n-inv (image x)))))))
  :props (zfc v-omega+$prop inverse$prop prod2$prop domain$prop v$prop))

; Start proof of in-cdr-assoc-implies-in-v-omega*2.  (Set theory lemmas
; cdr-preserves-in-for-transitive and car-preserves-in-for-transitive were
; originally proved here, as well as
; hons-assoc-equal-preserves-in-for-transitive.)

(defthmz in-v-omega*2-suff
  (implies (and (in x (v-omega+-n n))
                (natp n))
           (in x (v-omega*2)))
  :props (zfc v-omega+$prop inverse$prop prod2$prop domain$prop v$prop))

(defthmz in-cdr-hons-assoc-equal-implies-in-v-omega*2
  (implies (and (in hta (v-omega*2))
                (consp (hons-assoc-equal key hta))
                (in x (cdr (hons-assoc-equal key hta))))
           (in x (v-omega*2)))
  :props (zfc v-omega+$prop inverse$prop prod2$prop domain$prop v$prop)
  :instructions (:bash (:claim (in x (v-omega+-n (v-omega+-n-inv hta))))
                       (:rewrite in-v-omega*2-suff)))

(defthmz transitive-v-omega*2
; Idea of proof: Expand transitivite-p and then use
; in-v-omega+-implies-in-v-omega+-n and in-v-omega*2-suff.  The restrict
; hint was suggested by enabling transitive and subset in the proof-builder
; and, essentially after generaliing (probably not necessary), considering the
; free variable for in-v-omega*2-suff.
  (transitive (v-omega*2))
  :hints (("Goal"
           :restrict
           ((in-v-omega*2-suff
             ((n (v-omega+-n-inv (transitive-witness (v-omega*2)))))))
           :in-theory (enable transitive subset)))
  :props (zfc v-omega+$prop v$prop domain$prop prod2$prop inverse$prop))

(defthmz cons-in-v-omega*2-1
  (implies (consp x)
           (implies (in x (v-omega*2))
                    (and (in (car x) (v-omega*2))
                         (in (cdr x) (v-omega*2)))))
  :props (zfc v-omega+$prop inverse$prop prod2$prop domain$prop v$prop)
  :rule-classes nil)

(defthmz cons-in-v-omega*2-2
; Developed as follows, but when IN-POWERSET-POWERSET had its two subset hyps
; first, which isn't ideal (so I changed that since then).
#|
  :INSTRUCTIONS
  (:BASH
       (:USE (:INSTANCE IN-V-OMEGA*2-SUFF (X X)
                        (N (+ 2
                              (MAX (V-OMEGA+-N-INV (CAR X))
                                   (V-OMEGA+-N-INV (CDR X)))))))
       (:IN-THEORY (DISABLE IN-V-OMEGA*2-SUFF))
       :SPLIT (:CHANGE-GOAL NIL T)
       :PROVE (:CONTRAPOSE 1)
       (:DROP 1)
       (:BASH ("Goal" :EXPAND ((V-OMEGA+-N (+ 2 (V-OMEGA+-N-INV (CAR X))))
                               (V-OMEGA+-N (+ 2 (V-OMEGA+-N-INV (CDR X)))))))
       (:USE (:INSTANCE IN-POWERSET-POWERSET
                        (DOM (V-OMEGA+-N (V-OMEGA+-N-INV (CAR X))))
                        (RAN (V-OMEGA+-N (V-OMEGA+-N-INV (CDR X))))
                        (S (V-OMEGA+-N (MAX (V-OMEGA+-N-INV (CAR X))
                                            (V-OMEGA+-N-INV (CDR X)))))))
       :PROVE
       (:USE (:INSTANCE IN-POWERSET-POWERSET
                        (DOM (V-OMEGA+-N (V-OMEGA+-N-INV (CAR X))))
                        (RAN (V-OMEGA+-N (V-OMEGA+-N-INV (CDR X))))
                        (S (V-OMEGA+-N (MAX (V-OMEGA+-N-INV (CAR X))
                                            (V-OMEGA+-N-INV (CDR X)))))))
       :PROVE))
|#
  (implies (and (consp x)
                (in (car x) (v-omega*2))
                (in (cdr x) (v-omega*2)))
           (in x (v-omega*2)))
  :props (zfc v-omega+$prop inverse$prop prod2$prop domain$prop v$prop)
  :hints
  (("Goal"
    :in-theory (disable in-v-omega*2-suff)
    :expand ((v-omega+-n (+ 2 (v-omega+-n-inv (car x))))
             (v-omega+-n (+ 2 (v-omega+-n-inv (cdr x)))))
    :use ((:instance in-v-omega*2-suff (x x)
                     (n (+ 2
                           (max (v-omega+-n-inv (car x))
                                (v-omega+-n-inv (cdr x))))))))))

(defthmz cons-in-v-omega*2
  (implies (consp x)
           (equal (in x (v-omega*2))
                  (and (in (car x) (v-omega*2))
                       (in (cdr x) (v-omega*2)))))
  :props (zfc v-omega+$prop inverse$prop prod2$prop domain$prop v$prop)
  :hints (("Goal" :use (cons-in-v-omega*2-1 cons-in-v-omega*2-2))))

(defthmz prod2-in-v-omega*2
  (implies (and (in x (v-omega*2))
                (in y (v-omega*2)))
           (in (prod2 x y) (v-omega*2)))
  :hints (("Goal" :cases ((equal x 0) (equal y 0))))
  :props (zfc v-omega+$prop v$prop inverse$prop prod2$prop domain$prop))

(defthmz union2-in-v-omega*2
  (implies (and (in x (v-omega*2))
                (in y (v-omega*2)))
           (in (union2 x y) (v-omega*2)))
  :hints (("Goal" :use ((:instance in-v-omega*2-suff
                                   (x (union2 x y))
                                   (n (1+ (max (v-omega+-n-inv x)
                                               (v-omega+-n-inv y))))))))
  :props (zfc v-omega+$prop v$prop inverse$prop prod2$prop domain$prop))

; Start proof of zseqs-in-v-omega*2.  A proof sketch is below, but first,
; here is a useful general lemma.

(defthmz subset-powerset-v-omega+-n+1

; Note: I think we can do one better, i.e., replacing (1+ n) by n.  But we
; don't need that for the proof of zseqs-in-v-omega*2, which is what
; inspired this lemma.

; Proof. Given the hypotheses, if y \subset x then y \subset (v-omega+-n n) by
; transitivity of (v-omega+-n n); hence y \in (powerset (v-omega+-n n)) =
; (v-omega+-n (1+ n)).

  (implies (and (natp n)
                (in x (v-omega+-n n)))
           (subset (powerset x) (v-omega+-n (1+ n))))
  :props (zfc v-omega+$prop v$prop
              inverse$prop prod2$prop domain$prop)
  :hints (("Goal" :expand ((subset (powerset x)
                                    (powerset (v-omega+-n n)))))))

(defthmz in-powerset-v-omega+-n+2

; Note:  I think we can do one better, i.e., replacing (+ 2 n) by (1+ n).
; This is an immediate corollary of subset-powerset-v-omega+-n+1, which we
; may not need but seems worth stating. 

  (implies (and (natp n)
                (in x (v-omega+-n n)))
           (in (powerset x) (v-omega+-n (+ 2 n))))
  :props (zfc v-omega+$prop v$prop
              inverse$prop prod2$prop domain$prop)
  :hints (("Goal"
           :expand ((v-omega+-n (+ 2 n)))
           :in-theory (disable v-omega+-n))))

; The lemma in-omega-v-omega*2 below is necessary for L2 below.

(in-theory (disable (:e v-omega+-n)))

(encapsulate ()

(local (defthmz in-omega-v-omega*2-lemma
         (implies (subset x (v-omega))
                  (in x (v-omega+-n 1)))
         :hints (("Goal" :expand ((v-omega+-n 1))))
         :rule-classes nil))

(defthmz in-omega-v-omega*2
  (in (omega) (v-omega*2))
  :hints (("Goal" :use ((:instance in-omega-v-omega*2-lemma
                                   (x (omega))))))
  :props (zfc v-omega+$prop v$prop
              inverse$prop prod2$prop domain$prop))
)

(encapsulate ()

; Returning to the proof of zseqs-in-v-omega*2:

; L1. If f \in (zseqs x) then f \subset (prod2 (omega) x), hence f \in
; (powerset (prod2 (omega) x)); so (zseqs x) \subset (powerset (prod2
; (omega) x)).

; L2. Now (prod2 (omega) x) \in (v-omega*2) by prod2-in-v-omega*2; hence
; (prod2 (omega) x) \in (v-omega+-n n1) for n1 = (v-omega+-n-inv (prod2
; (omega) x)).

; L3. By L2 and subset-powerset-v-omega+-n+1, (powerset (prod2 (omega) x))
; \subset (v-omega+-n (1+ n1)).

; L4. By transitivity of subset, L1, and L3, (zseqs x) \subset
; (v-omega+-n (1+ n1)).

; L5. Thus (zseqs x) \in (v-omega+-n (+ 2 n1)).

; So (zseqs x) \in (v-omega*2).

(local
 (defthmz l1
   (subset (finseqs x)
           (powerset (prod2 (omega) x)))
   :props (zfc inverse$prop prod2$prop domain$prop finseqs$prop)
   :hints (("Goal" :in-theory (enable subset)))))

(local
 (defun n1 (x)
   (v-omega+-n-inv (prod2 (omega) x))))

(local
 (defthmz l2
   (implies (in x (v-omega*2))
            (in (prod2 (omega) x)
                (v-omega+-n (n1 x))))
   :props (zfc v-omega+$prop v$prop
               inverse$prop prod2$prop domain$prop)))

(local
 (defthmz l3
   (implies (in x (v-omega*2))
            (subset (powerset (prod2 (omega) x))
                    (v-omega+-n (1+ (n1 x)))))
   :hints (("Goal" :in-theory (disable v-omega+-n)))
   :props (zfc v-omega+$prop v$prop
               inverse$prop prod2$prop domain$prop)))

(local
 (defthmz l4
   (implies (in x (v-omega*2))
            (subset (finseqs x)
                    (v-omega+-n (1+ (n1 x)))))
   :hints (("Goal"
            :in-theory (disable n1 v-omega+-n)
            :restrict ((subset-transitivity
                        ((y (powerset (prod2 (omega) x))))))))
   :props (zfc v-omega+$prop v$prop
               inverse$prop prod2$prop domain$prop finseqs$prop)))

(local
 (defthmz l5
   (implies (in x (v-omega*2))
            (in (finseqs x)
                (v-omega+-n (+ 2 (n1 x)))))
   :hints (("Goal"
            :in-theory (disable n1 v-omega+-n)
            :expand ((v-omega+-n (+ 2 (n1 x))))))
   :props (zfc v-omega+$prop v$prop
               inverse$prop prod2$prop domain$prop finseqs$prop)))

(defthmz finseqs-in-v-omega*2
  (implies (in x (v-omega*2))
           (in (finseqs x) (v-omega*2)))
  :hints (("Goal"
           :restrict ((in-v-omega*2-suff ((n (+ 2 (n1 x))))))))
  :props (zfc v-omega+$prop v$prop
              inverse$prop prod2$prop domain$prop finseqs$prop))
)

(encapsulate ()

; We pattern the proof of fun-space-in-v-omega*2 after the proof of
; finseqs-in-v-omega*2.

; L1. If f \in (fun-space x y) then f \subset (prod2 x y), hence f \in
; (powerset (prod2 x y)); so (fun-space x y) \subset (powerset (prod2 x y)).

; L2. Now (prod2 x y) \in (v-omega*2) by prod2-in-v-omega*2; hence (prod2
; x y) \in (v-omega+-n n1) for n1 = (v-omega+-n-inv (prod2 x y)).

; L3. By L2 and subset-powerset-v-omega+-n+1, (powerset (prod2 x y))
; \subset (v-omega+-n (1+ n1)).

; L4. By transitivity of subset, L1, and L3, (fun-space x y) \subset
; (v-omega+-n (1+ n1)).

; L5. Thus (fun-space x y) \in (v-omega+-n (+ 2 n1)).

; So (fun-space x y) \in (v-omega*2).


(local
 (defthmz l1
   (subset (fun-space x y)
           (powerset (prod2 x y)))
   :props (zfc inverse$prop prod2$prop domain$prop fun-space$prop)
   :hints (("Goal" :in-theory (enable subset)))))

(local
 (defun n1 (x y)
   (v-omega+-n-inv (prod2 x y))))

(local
 (defthmz l2
   (implies (and (in x (v-omega*2))
                 (in y (v-omega*2)))
            (in (prod2 x y)
                (v-omega+-n (n1 x y))))
   :props (zfc v-omega+$prop v$prop
               inverse$prop prod2$prop domain$prop)))

(local
 (defthmz l3
   (implies (and (in x (v-omega*2))
                 (in y (v-omega*2)))
            (subset (powerset (prod2 x y))
                    (v-omega+-n (1+ (n1 x y)))))
   :hints (("Goal" :in-theory (disable v-omega+-n)))
   :props (zfc v-omega+$prop v$prop
               inverse$prop prod2$prop domain$prop)))

(local
 (defthmz l4
   (implies (and (in x (v-omega*2))
                 (in y (v-omega*2)))
            (subset (fun-space x y)
                    (v-omega+-n (1+ (n1 x y)))))
   :hints (("Goal"
            :in-theory (disable n1 v-omega+-n)
            :restrict ((subset-transitivity
                        ((y (powerset (prod2 x y))))))))
   :props (zfc v-omega+$prop v$prop
               inverse$prop prod2$prop domain$prop fun-space$prop)))

(local
 (defthmz l5
   (implies (and (in x (v-omega*2))
                 (in y (v-omega*2)))
            (in (fun-space x y)
                (v-omega+-n (+ 2 (n1 x y)))))
   :hints (("Goal"
            :in-theory (disable n1 v-omega+-n)
            :expand ((v-omega+-n (+ 2 (n1 x y))))))
   :props (zfc v-omega+$prop v$prop
               inverse$prop prod2$prop domain$prop fun-space$prop)))

(defthmz fun-space-in-v-omega*2
  (implies (and (in x (v-omega*2))
                (in y (v-omega*2)))
           (in (fun-space x y) (v-omega*2)))
  :hints (("Goal" :restrict ((in-v-omega*2-suff
                              ((n (+ 2 (n1 x y))))))))
  :props (zfc v-omega+$prop v$prop
              inverse$prop prod2$prop domain$prop fun-space$prop))
) ; end encapsulate

(defthmz in-cdr-hons-assoc-equal-in-v-omega*2
  (implies (in a (v-omega*2))
           (in (hons-assoc-equal key a) (v-omega*2)))
  :props (zfc v-omega+$prop v$prop
              inverse$prop prod2$prop domain$prop fun-space$prop))

(defthmz in-hol-type-eval-v-omega*2
  (implies (and (in hta (v-omega*2))
                (hol-typep type hta t))
           (in (hol-type-eval type hta) (v-omega*2)))
  :props (zfc v-omega+$prop v$prop
              inverse$prop prod2$prop domain$prop fun-space$prop
              finseqs$prop)
  :hints (("Goal" :in-theory (enable hol-type-eval))))

(defthmz hol-valuep-implies-in-v-omega*2
  (implies (and (in hta (v-omega*2))
                (hol-typep type hta t)
                (hol-valuep x type hta))
           (in x (v-omega*2)))
  :props (zfc v-omega+$prop v$prop
              inverse$prop prod2$prop domain$prop fun-space$prop
              finseqs$prop))

