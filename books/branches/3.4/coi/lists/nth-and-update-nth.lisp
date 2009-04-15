#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; nth-and-update-nth.lisp
;; Rules about nth and update-nth.

(in-package "LIST")

(include-book "basic")
(include-book "repeat")
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (e/d (len-of-cdr) (len))))

(in-theory (disable nth update-nth))

;; List Congruences
;; 
;; A first observation is that nth and update-nth respect equiv for their list
;; argument to some degree.

;; TEMP (jcd) - I added each of these rules.

(defcong equiv equal (nth n l) 2 :hints (("Goal" :in-theory (enable nth))))
(defcong equiv equiv (update-nth n v l) 3 :hints (("Goal" :in-theory (enable update-nth))))





;; Type Rules
;;
;; jcd - Note that true-listp-update-nth is redundant with ACL2's built in
;; rule, but I wanted to add it anyway just to show that we have it.  (Also,
;; note that the name true-listp-update-nth is shared with the ACL2 package
;; because it is a member of *acl2-exports*)

(defthm true-listp-update-nth
  (implies (true-listp ACL2::l)
           (true-listp (update-nth ACL2::key ACL2::val ACL2::l)))
  :rule-classes :type-prescription)

(defthm true-listp-update-nth-rewrite
  (implies (true-listp l)
           (true-listp (update-nth n v l))))




;; Theorems about Nth

(defthm nth-when-l-is-not-a-consp
  (implies (not (consp l))
           (equal (nth n l)
                  nil))
  :hints (("Goal" :in-theory (enable nth))))

(defthm nth-of-cons
  (equal (nth n (cons x y))
         (if (zp n)
             x
           (nth (+ -1 n) y)))
  :hints (("Goal" :in-theory (enable nth))))

;; jcd - this rule is inspired by the standard list-defthms book, but is 
;; improved by dropping the true-listp hyp.

(defthm nth-with-large-index
  (implies (<= (len l) (nfix n))
           (equal (nth n l)
                  nil))
  :hints(("Goal" :in-theory (enable nth))))

;; jcd - copied this rule from the data-structures/list-defthms.lisp file,
;; and this is strong enough to prove update-nth-update-nth-diff below 
;; without even including data-structures/list-defthms.  BTW, I think there
;; are going to be lots of useful rules in the data-structures library that
;; we haven't included yet.

(defthm nth-append
  (equal (nth n (append a b))
         (if (< (nfix n) (len a))
             (nth n a)
           (nth (- (nfix n) (len a))
                b)))
  :hints(("Goal" :in-theory (enable nth))))

;; jcd - copied this rule from the data-structures/list-defthms.lisp file, it
;; is useful in the proof of firstn-update-nth-array, and seems to be a
;; generally good rule to have.

(defthm nth-firstn
  (equal (nth i (firstn j l))
         (if (< (nfix i) (nfix j))
             (nth i l)
             nil))
  :hints (("Goal" :in-theory (enable firstn nth))))

;; jcd - copied this rule from the data-structures/list-defthms.lisp file, it
;; is useful in the proof of nthcdr-update-nth-array and seems generally to be
;; a good rule.

(defthm nth-nthcdr
  (equal (nth i (nthcdr j l))
         (nth (+ (nfix j) (nfix i))
              l))
  :hints(("Goal" :in-theory (enable nthcdr nth))))

;; jcd - added this rule, inspired by list-defthms.lisp, but modified for 
;; repeat instead of make-list-ac.

(encapsulate
 ()

 (local (defun double-sub1-induct (n1 n2)
          (if (not (zp n1))
              (double-sub1-induct (1- n1) (1- n2))
            n2)))
 
 (defthm nat-repeat
   (equal (nth i (repeat j v))
          (if (< (nfix i) (nfix j))
              v
            nil))
   :hints(("Goal" :in-theory (enable repeat nth)
           :induct (double-sub1-induct i j))))
)
           

;; Theorems about Update-Nth
;;
;; Unlike nth above, we actually have quite a few theorems to prove about
;; update-nth.

(local (in-theory (disable update-nth)))

;; TEMP (jcd) - generalized this theorem to non-consp.  Originally it was:
;;
;; (defthm update-nth-nil
;;   (equal (update-nth n v nil)
;;          (append (repeat n nil) 
;;                  (list v)))
;;   :hints (("Goal" :in-theory (enable update-nth append))))

;; bzo (jcd) - make this local since it mentions repeat?  (do we want the
;; repeat-mentioning theorems to be local?)

(defthm update-nth-non-consp
  (implies (not (consp l))
           (equal (update-nth n v l)
                  (append (repeat n nil)
                          (list v))))
  :hints(("Goal" :in-theory (enable repeat update-nth))))

(defthm update-nth-when-key-is-not-an-integerp
  (implies (not (integerp key))
           (equal (update-nth key val lst)
                  (update-nth 0 val lst)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm update-nth-when-key-is-not-positive
  (implies (and (<= key 0)
                (syntaxp (not (equal ''0 key))))
           (equal (update-nth key val lst)
                  (update-nth 0 val lst)))
  :hints (("Goal" :in-theory (enable update-nth))))


;; TEMP (jcd) removed this rule since it is now subsumed by
;; update-nth-non-consp.  Previous comment asked if we can just say what 
;; update-nth is equal to in the non-consp case, and indeed, we just did.
;;
;; (defthm len-update-nth-ncons
;;   (implies (not (consp l))
;;            (equal (len (update-nth n v l))
;;                   (1+ (nfix n))))
;;   :hints (("Goal" :in-theory (enable len update-nth))))

;; jcd - ACL2 has a built-in rule called len-update-nth, which is inferior
;; to the following rule and only fires under certain hypotheses.  We will
;; replace this rule with our better rule, and then disable the original,
;; weak rule since it is no longer necessary.
;;
;; bzo (jcd) - Matt Kaufmann says that in v2.9.3 and beyond, the built in 
;; len-update-nth rule will be changed to this.  After v2.9.3, we should 
;; remove this disable and this rule, and use the built in rule instead.
;;
;; TEMP (jcd) - added this to disable the original rule.

(in-theory (disable len-update-nth))

(defthm len-update-nth-better
  (equal (len (update-nth n val x))
         (max (1+ (nfix n)) 
              (len x)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm car-of-update-nth
  (equal (car (update-nth key val l))
         (if (zp key)
             val
           (car l)))
  :hints(("Goal" :in-theory (enable update-nth))))

(defthm fix-of-update-nth 
  (equal (fix (update-nth key val l))
         (if (< (nfix key) (len l))
             (update-nth key val (fix l))
           (append l (repeat (+ key (- (len l))) nil) (list val))))
  :hints(("Goal" :in-theory (e/d (repeat update-nth) 
                                 (list-equiv-hack ;bzo
                                  )))))

;; bzo (jcd) - add a rule for cdr of update nth?      

;; TEMP (jcd) - this rule was originally named update-nth-update-nth-better and
;; was a replacement for ACL2::update-nth-update-nth as provided by the
;; data-structures/list-defthms book, which we were previously including.
;; However, we can prove it without including that book, and since we are in
;; our own namespace now, we can give it the name it ought to have,

(defthm update-nth-update-nth
  (equal (update-nth j b (update-nth i a l))
         (if (equal (nfix i) (nfix j))
             (update-nth j b l)
           (update-nth i a (update-nth j b l))))           
  :rule-classes
  ((:rewrite :corollary
             (implies (equal (nfix i) (nfix j))
                      (equal (update-nth j b (update-nth i a l))
                             (update-nth j b l))))
   (:rewrite :loop-stopper ((j i))
             :corollary
             (implies (< (nfix i) (nfix j))
                      (equal (update-nth j b (update-nth i a l))
                             (update-nth i a (update-nth j b l))))))
  :hints(("Goal" :in-theory (enable update-nth))))

;; bzo (jcd) - can we strengthen this rule by dropping the hyps and adding 
;; nfixes?

(defthm firstn-update-nth
  (implies (and (integerp n)
                (<= 0 n)
                (integerp n2)
                (<= 0 n2))
           (equal (firstn n (update-nth n2 v l))
                  (if (<= n n2)
                      (append (firstn n l) (repeat (- n (len l)) nil))
                    (update-nth n2 v (firstn n l)))))
  :hints (("Goal" :in-theory (enable firstn repeat update-nth))))

(defthm nthcdr-update-nth
  (implies (and (integerp n)
                (<= 0 n)
                (integerp n2)
                (<= 0 n2))
           (equal (nthcdr n (update-nth n2 v l))
                  (if (< n2 n)
                      (nthcdr n l)
                    (update-nth (- n2 n) v (nthcdr n l)))))
  :hints (("Goal" :in-theory (enable nthcdr update-nth))))



;bzo why is repeat here?
;trying disabled, since we have update-nth-equal-rewrite. -ews
(defthmd equal-update-nth-casesplit
  (implies (and (integerp n)
                (<= 0 n))
           (equal (equal (update-nth n v l1) l2)
                  (and (equal (nth n l2) v)
                       (< n (len l2))
                       (equal (firstn n (append l1 (repeat (- n (len l1)) nil))) (firstn n l2))
                       (equal (nthcdr (1+ n) l1) (nthcdr (1+ n) l2)))))
  :hints (("Goal" :in-theory (enable nth update-nth 
                                     repeat ;bzo why?
                                     ))))


(defthmd equal-update-nth-update-nth
  (implies (and (integerp n)
                (<= 0 n)
                (equal (len l1) (len l2)))
  (equal (equal (update-nth n v1 l1) (update-nth n v2 l2))
         (and (equal v1 v2)
              (equal (firstn n l1) (firstn n l2))
              (equal (nthcdr (1+ n) l1) (nthcdr (1+ n) l2)))))
  :hints (("Goal" :in-theory (enable update-nth nth))))

(defthm nth-update-nth-better
  (implies (and (syntaxp (quotep n1))
                (syntaxp (quotep n2)))
           (equal (nth n1 (update-nth n2 v l))
                  (if (equal (nfix n1) (nfix n2))
                      v
                    (nth n1 l))))
  :hints (("Goal" :in-theory (enable nth update-nth))))

(defthm update-nth-update-nth-diff
  (implies (not (equal (nfix i1) 
                       (nfix i2)))
           (equal (update-nth i1 v1 (update-nth i2 v2 l))
                  (update-nth i2 v2 (update-nth i1 v1 l))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable update-nth 
                              nthcdr ;why?
                              )))
  :rule-classes ((:rewrite :loop-stopper ((i1 i2)))))

(defthm update-nth-update-nth-same
  (equal (update-nth i v1 (update-nth i v2 l))
         (update-nth i v1 l))
  :hints (("Goal" :in-theory (enable update-nth))))

;; jcd - this is a nice rule from the list-defthms book, which we have copied
;; verbatim.

(defthm update-nth-append
  (equal (update-nth n v (append a b))
         (if (< (nfix n) (len a))
             (append (update-nth n v a) b)
           (append a (update-nth (- n (len a)) v b))))
  :hints(("Goal" :in-theory (enable update-nth))))





(defund clear-nth (key lst)
  (update-nth key nil lst))
  
;bzo handle this better!
(defthm update-nth-equal-update-nth-rewrite
  (implies (AND (syntaxp (not (and (equal val2 ''nil)
                                   (equal val1 ''nil)))) ;prevents loops
                (INTEGERP key)
                (<= 0 key)
                (EQUAL (LEN L1) (LEN L2)) ;yuck!
                )
           (equal (equal (update-nth key val1 l1) (update-nth key val2 l2))
                  (and (equal val1 val2)
                       (equal (clear-nth key l1) (clear-nth key l2)))))
  :hints (("Goal" :in-theory (enable clear-nth
                                     LIST::EQUAL-UPDATE-NTH-UPDATE-NTH))))


(defthm clear-nth-of-update-nth
  (equal (clear-nth key1 (update-nth key2 val lst))
         (if (equal (nfix key1) (nfix key2))
             (clear-nth key1 lst)
           (update-nth key2 val (clear-nth key1 lst))))
  :hints (("Goal" :in-theory (enable clear-nth))))

(defthm clear-nth-of-clear-nth
  (equal (clear-nth key1 (clear-nth key2 lst))
         (clear-nth key2 (clear-nth key1 lst))
         )
  :RULE-CLASSES
  ((:REWRITE :LOOP-STOPPER ((key1 key2))))
  :hints (("Goal" :cases ((equal (nfix key1) (nfix key2)))
           :in-theory (enable clear-nth))))

(defthm len-of-clear-nth
  (equal (len (clear-nth key lst))
         (max (len lst) (+ 1 (nfix key))))
  :hints (("Goal" :in-theory (enable clear-nth))))

(defthm nth-of-clear-nth
  (equal (nth n1 (clear-nth n2 lst))
         (if (equal (nfix n1) (nfix n2))
             nil
           (nth n1 lst)))
  :hints (("Goal" :in-theory (enable clear-nth))))

;t-p rule? 
(defthm true-listp-of-clear-nth
  (implies (true-listp lst)
           (true-listp (clear-nth n lst)))
  :hints (("Goal" :in-theory (enable clear-nth))))


(defthm update-nth-equal-rewrite
  (equal (equal (update-nth n val lst1) lst2)
         (and (equal val (nth (nfix n) lst2))
              (< (nfix n) (len lst2)) ;this seems to be causing slowdown...
              (equal (clear-nth n lst1) (clear-nth n lst2))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;LIST::EQUAL-UPDATE-NTH-CASESPLIT
;                      LIST::LEN-OF-CDR 
                       UPDATE-NTH 
                       clear-nth
                       nth
                       ))))


;this might be expensive, so we disable it... -ews
;perhaps we don't need this if we have update-nth-equal-rewrite. -ews
;but perhaps we need it to to get nice expected result functions for symbolic simulation...
(defthmd update-nth-with-what-was-already-there
  (implies (and (equal x (nth (nfix k) st))
                (< (nfix k) (len st))
                )
           (equal (update-nth k x st)
                  st
                  )))

;not true!
;; (defcong equiv equal (clear-nth n l) 2 
;;   :hints (("Goal" :in-theory (e/d (clear-nth) 
;;                                   ( looped:
;;                                    UPDATE-NTH-EQUAL-REWRITE)))))

;; jcd - this is a nice rule inspired by list-defthms.  We have improved the
;; rule slightly by dropping the true-listp hypothesis.

(defthm update-nth-nth
  (implies (and (integerp n)
                (<= 0 n)
                (< n (len l)) ;move this into the conclusion?
                )
           (equal (update-nth n (nth n l) l)
                  l)))







;; Dead Rules!

;; TEMP (jcd) - This is exactly the same as nthcdr-of-zp, removing it.
;;
;; (defthm nthcdr-0
;;   (implies (zp n)
;;            (equal (nthcdr n l)
;;                   l))
;;   :hints (("goal" :in-theory (enable nthcdr))))

;; TEMP (jcd) - This is subsumed by nthcdr-of-non-consp, so I have removed it.
;;
;; (defthm nthcdr-nil
;;   (equal (nthcdr n nil)
;;          nil)
;;   :hints (("Goal" :in-theory (enable nthcdr))))

;; TEMP (jcd) - This is redundant now that LIST::firstn and ACL2::firstn are the
;; same.
;;
;; (defthm firstn-of-cons
;;   (equal (list::firstn n (cons a l))
;;          (if (zp n)
;;              nil
;;            (cons a (list::firstn (+ -1 n) l)))))

;; TEMP (jcd) - This rule was originally called firstn-with-large-index-better,
;; and was intended as a replacement for ACL2::firstn-with-large-index as
;; provided by data-structures/list-defthms, which we were previously
;; including.  However, this is actually an exact copy of the rewrite rule
;; firstn-does-nothing, which is proven in basic.lisp, so I have removed it.
;;
;; (defthm firstn-with-large-index
;;   (implies (<= (len l) (nfix n))
;;            (equal (firstn n l)
;;                   (fix l))))        


;; TEMP (jcd) - Comments asked if this could be removed, and indeed it seems
;; that we can remove it without a problem.  So, I have done so.
;;
;; (defthmd equal-len-n
;;   (implies
;;    (syntaxp (quotep n))
;;    (equal (equal (len x) n)
;;           (if (integerp n)
;;               (if (< n 0)
;;                   nil
;;                   (if (equal n 0)
;;                       (atom x)
;;                       (and (consp x)
;;                            (equal (len (cdr x)) (- n 1)))))
;;               nil)))
;;   :hints (("goal" :in-theory (enable len))))

;; TEMP (jcd) - Removed this since we now have a congruence rule about nth.
;;
;; (defthm nth-fix-true-listp
;;   (equal (nth n (list::fix l))
;;          (nth n l))
;;   :hints (("goal" :in-theory (enable nth))))

;; TEMP (jcd) - Removed this because we know that append is congruent in its
;; first argument.
;;
;; (defthm append-fix-true-listp
;;   (equal (append (list::fix a) b)
;;          (append a b)))

;; TEMP (jcd) - This theorem was disabled (defthmd) and wasn't being used
;; anywhere, so I took it out.
;;
;; (defthmd update-nth-over
;;   (implies (and (<= (len l) n)
;;                 (integerp n)
;;                 (<= 0 n))
;;            (equal (update-nth n v l)
;;                   (append 
;;                    l
;;                    (append (repeat (- n (len l)) nil)
;;                            (list v)))))
;;   :hints (("goal" :in-theory (enable len update-nth append))))

;; TEMP (jcd) - Comments indicated that the following theorem should be dropped
;; since we have firstn-cons, and so I have dropped it.
;;
;; (defthmd firstn-1-element
;;   (equal (firstn n (cons a nil)) 
;;          (if (< 0 (nfix n))
;;              (cons a nil)
;;            nil)))

;; TEMP (jcd) - We actually have a stronger rule, append-equal-self-one, so I
;; am getting rid of this.
;;
;; (defthm equal-a-append-a-b
;;   (equal (equal a (append a b))
;;          (or (and (not (consp a))
;;                   (equal a b))
;;              (equal b (list::finalcdr a)))))

;; TEMP (jcd) - The following rule is redundant with len-of-firstn, so I am 
;; removing it.
;;
;; (defthm len-firstn-better
;;   (equal (len (firstn n l))
;;          (min (nfix n) (len l))))

;; TEMP (jcd) - I think we should remove these old comments.
;;
;; dsh
;; (defthm equal-fix-true-listp-firstn
;;   (equal
;;    (equal (acl2::fix-true-listp l) (firstn n l))
;;    (<= (len l) (nfix n)))
;;   :hints (("goal" :in-theory (enable firstn len))))  
;;
;; dsh
;; (defthm nthcdr-fix-true-listp
;;   (equal
;;    (nthcdr n (fix-true-listp l))
;;    (firstn (- (len l) (nfix n)) (nthcdr n l)))
;;   :hints (("goal" :in-theory (enable nthcdr firstn len))))
;;
;; (defthm firstn-fix-true-listp
;;   (equal (firstn n (fix-true-listp l))
;;          (firstn n l))
;;   :hints (("goal" :in-theory (enable firstn))))
;;   
;; dsh
;; (defthm fix-true-listp-update-nth
;;   (equal
;;    (update-nth n v (fix-true-listp l))
;;    (fix-true-listp (update-nth n v l)))
;;   :hints (("goal" :in-theory (enable update-nth nth nthcdr firstn))))
;;  
;; BY: These gave problems in acl2-v2.8 because 
;;     nth-update-nth was disable in favor of a new
;;     nth-update-nth-better that doesn't fire. 

;; (TEMP) jcd - removed this rule since we already have len-of-nthcdr.
;;
;; (defthm len-nthcdr-alt
;;   (equal (len (nthcdr n list))
;;          (nfix (- (len list) (nfix n))))
;;   :hints (("goal" :in-theory (enable acl2::default-cdr))))

;; TEMP (jcd) - removed this rule because we already have a stronger rule
;; called nthcdr-of-cons, which I have now enabled.
;;
;; (defthm nthcdr-cons-2
;;   (implies (not (zp n))
;;            (equal (nthcdr n (cons a b))
;;                   (nthcdr (1- n) b)))
;;   :hints (("goal" :in-theory (enable nthcdr))))


            
;From eric's lemmas.  Drat.  I'm going to have to leave this disabled because
;it causes big problems when ACL2 rewrites an equality of two update-nth
;expressions.  Why?  Well, when ACL2 rewrites an equality of two known-consps,
;it tries to rewrite the equality of the cars and (sometimes) the equality of
;the cdrs.  In this case, that causes cdr-of-update-nth to fire and for some
;reason things start taking forever (probably because after pusing the cdr
;inside we are again left with an equality of two update-nth nests, albeit a
;smaller one).  Why that car-cdr hack is in the ACL2 code instead of being left
;to a rule is a mystery to me.  -EWS
(defthmd cdr-of-update-nth
  (equal (cdr (update-nth n val list))
         (if (zp n)
             (cdr list)
           (update-nth (+ -1 n) val (cdr list))))
  :hints (("Goal" :in-theory (enable update-nth))))

(local (in-theory (enable cdr-of-update-nth)))

(defthm clear-nth-of-append
  (implies (natp n)
           (equal (list::clear-nth n (append x y))
                  (if (< n (len x))
                      (append (list::clear-nth n x) y)
                    (append x (list::clear-nth (- n (len x)) y)))))
  :hints (("Goal" :in-theory (enable list::clear-nth))))

;gen to clear-nth-of-cons?
(defthm clear-nth-0-of-singleton
  (equal (list::clear-nth 0 (list val))
         (list nil))
  :hints (("Goal" :do-not '(preprocess) ;yikes...
           :in-theory (e/d (list::clear-nth) (LIST::UPDATE-NTH-EQUAL-REWRITE)))))

;is this right?
(theory-invariant (incompatible (:definition list::clear-nth) (:rewrite LIST::UPDATE-NTH-EQUAL-REWRITE)))

(defthm clear-nth-of-nil
  (equal (list::clear-nth n nil)
         (repeat (+ 1 (nfix n)) nil))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (list::clear-nth) (LIST::UPDATE-NTH-EQUAL-REWRITE)))))
        
(defthmd update-nth-of-cdr
  (implies (natp n)
           (equal (UPDATE-NTH n val (CDR LST))
                  (if (consp lst)
                      (cdr (UPDATE-NTH (+ 1 n) val LST))
                    (UPDATE-NTH n val nil))))
  :hints (("Goal" :in-theory (e/d (DEFAULT-CDR)
                                  ())
           :do-not '(generalize eliminate-destructors)))
  :otf-flg t)

(theory-invariant (incompatible (:rewrite UPDATE-NTH-OF-CDR) (:rewrite CDR-OF-UPDATE-NTH)))

;bzo may loop with defn nth?
(defthm nth-n-minus-one-of-cdr
  (implies (natp n)
           (equal (nth (+ -1 n) (cdr lst))
                  (if (zp n)
                      (cadr lst) ;kind of that nth returns the car when given n=-1
                    (if (consp lst)
                        (nth n lst)
                      nil))))
  :hints (("Goal" :in-theory (enable nth))))

;from eric
(defthm nth-of-cdr
  (equal (nth n (cdr lst))
         (nth (+ 1 (nfix n)) lst))
  :hints (("Goal" :in-theory (enable nth))))

(defthm update-nth-0-with-singleton
  (equal (update-nth 0 val1 (list val2))
         (list val1)))

(defthmd nth-0-becomes-car
  (equal (nth 0 lst)
         (car lst)))



;bzo handle non-zero?
(defthm cdr-of-update-nth-0
  (equal (cdr (update-nth 0 val lst))
         (cdr lst))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm clear-nth-of-clear-nth-same
  (equal (clear-nth n (clear-nth n r))
         (clear-nth n r))
  :hints (("Goal" :in-theory (e/d (clear-nth) (update-nth-equal-rewrite)))))

(defthm update-nth-becomes-clear-nth
  (equal (update-nth n nil r) 
         (clear-nth n r)))

(theory-invariant (incompatible (:rewrite update-nth-becomes-clear-nth) (:definition clear-nth)))

(defthm car-of-clear-nth
  (equal (car (clear-nth key l))
         (if (zp key)
             nil
           (car l)))
  :hints(("Goal" :in-theory (e/d (clear-nth) (UPDATE-NTH-BECOMES-CLEAR-NTH
                                              UPDATE-NTH-EQUAL-REWRITE)))))

(defthmd cdr-of-clear-nth
  (equal (cdr (clear-nth n list))
         (if (zp n)
             (cdr list)
           (clear-nth (+ -1 n) (cdr list))))
  :hints(("Goal" :in-theory (e/d (clear-nth) (UPDATE-NTH-BECOMES-CLEAR-NTH
                                              UPDATE-NTH-EQUAL-REWRITE)))))
(defthmd clear-nth-of-cdr
  (implies (natp n)
           (equal (clear-nth n (cdr lst))
                  (if (consp lst)
                      (cdr (clear-nth (+ 1 n) lst))
                    (clear-nth n nil))))
  :hints (("Goal" :in-theory (e/d (default-cdr
                                    clear-nth)
                                  (list::update-nth-becomes-clear-nth
                                   list::update-nth-equal-rewrite
                                   ))
           :do-not '(generalize eliminate-destructors)))
  :otf-flg t)


(defthm update-nth-of-cons
  (equal (list::update-nth n v (cons a lst))
         (if (zp n)
             (cons v lst)
           (cons a (list::update-nth (+ -1 n) v lst))))
  :hints (("Goal" :in-theory (enable list::update-nth))))

(defthm clear-nth-of-cons
  (equal (list::clear-nth n (cons a lst))
         (if (zp n)
             (cons nil lst)
           (cons a (list::clear-nth (+ -1 n) lst))))
  :hints (("Goal" :in-theory (e/d (list::clear-nth) 
                                  (LIST::UPDATE-NTH-BECOMES-CLEAR-NTH
                                   LIST::UPDATE-NTH-EQUAL-REWRITE)))))


(defthm list::firstn-clear-nth
  (implies (and (integerp n)
                (<= 0 n)
                (integerp list::n2)
                (<= 0 list::n2))
           (equal (firstn n (list::clear-nth list::n2 l))
                  (if (<= n list::n2)
                      (append (firstn n l)
                              (repeat (- n (len l)) nil))
                    (list::clear-nth list::n2 (firstn n l)))))
  :hints (("Goal" :in-theory (e/d (list::clear-nth) (LIST::UPDATE-NTH-EQUAL-REWRITE
                                                     list::update-nth-becomes-clear-nth
                                                     )))))

(defthm list::nthcdr-clear-nth
  (implies (and (integerp n)
                (<= 0 n)
                (integerp list::n2)
                (<= 0 list::n2))
           (equal (nthcdr n (list::clear-nth list::n2 l))
                  (if (< list::n2 n)
                      (nthcdr n l)
                    (list::clear-nth (- list::n2 n) (nthcdr n l)))))
  :hints (("Goal" :in-theory (e/d (list::clear-nth) (LIST::UPDATE-NTH-EQUAL-REWRITE
                                                     list::update-nth-becomes-clear-nth)))))

;; Pretty aggressive.  Splits each list into two parts: the part before element n and the
;; part after element n.
;bzo more general clear-nth-equal-rewrite?
(defthm clear-nth-equal-clear-nth-rewrite
  (implies (and (equal (len x) (len y))
                (integerp n)
                (<= 0 n))
           (equal (equal (list::clear-nth n x) (list::clear-nth n y))
                  (AND (EQUAL (FIRSTN N x)
                              (FIRSTN N y))
                       (EQUAL (NTHCDR (1+ N) x)
                              (NTHCDR (1+ N) y)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((nthcdr 1 x) ;bzo
                    (nthcdr 1 y))
           :in-theory (e/d (list::clear-nth
                            list::equal-update-nth-update-nth) 
                           (list::update-nth-equal-rewrite
                            list::update-nth-becomes-clear-nth
;                            AAMP::EQUAL-OF-IF
                            update-nth)))))

        
;phrased in this funny way so we don't have to decide to unilaterally write one into the other..
(defthm nth-0-equal-car
  (equal (equal (nth 0 lst) (car lst))
         t))

(defthm nth-when-n-is-not-an-integerp
  (implies (not (integerp n))
           (equal (nth n l)
                  (car l))))
