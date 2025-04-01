; Mixed rules about lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Organize these rules into simpler books.

;(include-book "kestrel/utilities/smaller-termp" :dir :system)
(include-book "kestrel/typed-lists-light/items-have-len" :dir :system) ; drop
;(include-book "repeat" )
(include-book "all-same" )
;(include-book "memberp" )
(include-book "memberp2" )
(include-book "update-subrange2" )
;(include-book "repeat-tail" )
;(include-book "perm" )
(include-book "subrange" )
;(include-book "reverse-list" )
(include-book "firstn" )
(include-book "all-equal-dollar2" )
;(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "take2" ))
(local (include-book "len" ))
(local (include-book "cons" ))
(local (include-book "nth" ))
(local (include-book "last" ))
(local (include-book "cdr" ))
(local (include-book "update-nth" ))
(local (include-book "perm2"))
;(local (include-book "clear-nth"))
(local (include-book "append" ))
(local (include-book "true-list-fix" ))
(local (include-book "take" ))
(local (include-book "nthcdr" ))
(local (include-book "subsetp-equal" ))
(local (include-book "no-duplicatesp-equal"))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

(in-theory (disable take)) ; drop?

;; todo: consider putting back the stuff with finalcdr

;bozo had to enable take a lot to prove subrange rules - prove take rules first instead??

;; (in-theory (disable take))

;; (defthm take-becomes-firstn
;;   (implies (< n (len lst))
;;            (equal (take n lst)
;;                   (firstn n lst)))
;;   :hints (("Goal" :in-theory (enable take firstn))))

;; (defthmd firstn-lemma-hack
;;  (IMPLIES (AND (EQUAL (NTH N LST1) (NTH N LST2))
;;                (< 0 N)
;;                (INTEGERP N)
;;                (EQUAL (FIRSTN N LST1)
;;                       (FIRSTN N LST2))
;;                (< (+ 1 n) (len lst1))
;;                (< (+ 1 n) (len lst2))
;;                )
;;           (EQUAL (FIRSTN (+ 1 N) LST1)
;;                  (FIRSTN (+ 1 N) LST2)))
;;  :hints (("Goal" :in-theory (enable firstn nth)
;;           :induct t
;;           :do-not '(generalize eliminate-destructors))))

;bozo gen!
(defthm subrange-of-update-nth-hack
  (implies (and; (< n (len lst)) ;bozo drop?
                (integerp n)
                (<= 0 n) ;gen?
                )
           (equal (SUBRANGE 0 n (UPDATE-NTH n val lst))
                  (append (SUBRANGE 0 (+ -1 n) lst) (list val))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (take subrange update-nth append equal-of-append)
                           (take-update-nth)))))

;(local (in-theory (enable equal-of-append)))

;bozo do this stuff better...
(defthm subrange-of-update-nth-hack-expensive
  (implies (and (equal m n)
;                (< n (len lst)) ;bozo drop?
                (integerp n)
                (<= 0 n) ;gen?
                )
           (equal (SUBRANGE 0 n (UPDATE-NTH m val lst))
                  (append (SUBRANGE 0 (+ -1 n) lst) (list val))))
  :hints (("Goal" :in-theory (enable equal-of-append)))
  ;; :hints (("Goal" :do-not '(generalize eliminate-destructors)
  ;;          :in-theory (e/d (subrange update-nth append) (take-update-nth))))
  )

(local
 (defun double-cdr-induct (x y)
   (if (endp x)
       (list x y)
     (double-cdr-induct (cdr x) (cdr y)))))

(defthmd equal-when-equal-of-car-and-car
  (implies (and (equal (car x) (car y))
                (consp x)
                (consp y))
           (equal (equal x y)
                  (equal (cdr x) (cdr y)))))

;move
;newly disabled
(defthmd equal-when-last-items-equal
  (implies (and (equal (len lst1) (len lst2))
                (equal (nth (+ -1 (len lst1)) lst1)
                       (nth (+ -1 (len lst1)) lst2))
                (true-listp lst1)
                (true-listp lst2)
                )
           (equal (equal lst1 lst2)
                  (equal (take (+ -1 (len lst1)) lst1)
                         (take (+ -1 (len lst1)) lst2))))
  :hints (("Goal" :in-theory (e/d (take ;len
                                   nth-of-0
                                   equal-when-equal-of-car-and-car
                                   )
                                  (len
                                   CONSP-FROM-LEN-CHEAP ;why?
                                   TAKE-OF-CDR
                                   ;;TRUE-LISTP
                                   cdr-iff ;disable?
                                   ))
           :induct (double-cdr-induct lst1 lst2)
           :do-not '(generalize eliminate-destructors))))

;move
(defthm memberp-when-perm-of-update-nth
  (implies (perm x (update-nth n a y))
           (memberp a x))
  :hints (("Goal" :in-theory (enable UPDATE-NTH))))

(local (in-theory (disable NTH-OF-CDR)))

(defthmd memberp-nth-and-cdr-safe
  (implies (and (< n (len lst))
                (and (integerp n) (< 0 n)))
           (memberp (nth n lst) (cdr lst)))
  :hints (("Goal" :in-theory (e/d (nth
                                   nth-when-n-is-zp)
                                  (;cancel_plus-lessp-correct
                                   ))
           :do-not '(generalize eliminate-destructors))))

;this can loop if we are turning car into nth 0...
(defthmd memberp-nth-and-cdr
  (implies (< n (len lst))
           (equal (memberp (nth n lst) (cdr lst))
                  (or (and (integerp n) (< 0 n))
                      (memberp (car lst) (cdr lst)))))
  :hints (("Goal" :in-theory (e/d (nth
                                   nth-when-n-is-zp)
                                  (;cancel_plus-lessp-correct
                                   ))
           :do-not '(generalize eliminate-destructors))))

(theory-invariant (incompatible (:rewrite memberp-nth-and-cdr) (:rewrite CAR-BECOMES-NTH-OF-0)))

;; (thm
;;  (equal (MEMBERP (CAR LST) (BAG::REMOVE-1 (NTH N LST) LST))

;can loop with nth-of-cdr
;rename
(defthmd nth-equal-car
  (implies (and (< n (len lst))
                (<= 0 n) ;not logically necessary
                )
           (equal (equal (nth n lst) (car lst))
                  (if (zp n)
                      t
                    (equal (nth (+ -1 n) (cdr lst)) (car lst)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable nth))))

;; (defthmd update-nth-rewrite-helper
;;   (implies (and (< n (len lst))
;;                 (<= 0 n)
;;                 (integerp n)
;;                 )
;;            (equal (update-nth n val lst)
;;                   (append (take n lst)
;;                           (list val)
;;                           (nthcdr (+ 1 n) lst))))
;;   :hints (("Goal" :in-theory (enable update-nth take nthcdr))))

(defthmd update-nth-rewrite
  (implies (< n (len lst))
           (equal (update-nth n val lst)
                  (append (take (nfix n) lst)
                          (list val)
                          (nthcdr (+ 1 (nfix n)) lst))))
  :hints (("Goal" :in-theory (enable update-nth take nthcdr))))

(defthm update-nth-rewrite-perm
  (implies (and (< n (len lst))
                (<= 0 n)
                (integerp n)
                )
           (perm (update-nth n val lst)
                 (append (take n lst)
                         (list val)
                         (nthcdr (+ 1 n) lst))))
  :hints (("Goal" :in-theory (enable  update-nth-rewrite))))

;; (thm
;;  (implies (and (integerp n)
;;                (<= 0 n)
;;                (< n (len lst)))
;;           (perm (BAG::REMOVE-1 val (UPDATE-NTH n val lst))
;;                      (BAG::REMOVE-1 (nth n lst) lst)))
;;  :hints (("Goal" :in-theory (e/d (update-nth bag::remove-1 perm nth-equal-car) (nth-of-cdr))
;;           :do-not '(generalize eliminate-destructors))))

;; (defthm fw-2
;;   (implies (and (perm bag1 (update-nth n val bag2))
;;                 (< n (len bag2)))
;;            (perm (bag::remove-1 val bag1)
;;                       (bag::remove-1 (nth n bag2) bag2)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable UPDATE-NTH perm bag::remove-1))))


;; (thm
;;  (equal (perm bag1 (update-nth n val bag2))
;;         (and (memberp val bag1)
;;              (perm (bag::remove-1 val bag1)
;;                         (bag::remove-1 (nth n bag2) bag2))))
;;  :hints (("Goal" :in-theory (enable UPDATE-NTH))))


;maybe we need to change how we normalize bag constructors in a perm context...  now we move all the conses in front of the appends.  but maybe we should sort based on the index if there are calls to nth, take, and nthcdr around?

;; (thm
;;  (equal (PERM lst
;;                    (cons (NTH n lst) lst2))

(defthm cons-of-nth-and-nth-plus-1
  (implies (and (integerp n)
                (<= 0 n))
           (equal (cons (nth n lst) (cons (nth (+ 1 n) lst) lst2))
                  (append (subrange n (+ 1 n) lst) lst2)))
  :hints (("Goal" :in-theory (enable take CDR-OF-NTHCDR)
           :expand ((TAKE 2 (NTHCDR N LST))
                    (subrange n (+ 1 n) lst)))))

(defthm append-subrange-nthcdr
  (implies (and (equal n (+ 1 end))
                (< end (len lst)) ;BOZO new
                (<= start end)
                (<= 0 start)
                (force (integerp end))
                (force (integerp start))
                (force (true-listp lst)))
           (equal (append (subrange start end lst) (nthcdr n lst))
                  (nthcdr (+ n -1 (- start end)) lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable take subrange nthcdr-of-cdr-combine-strong equal-of-append))))

(defthm append-nthcdr-subrange
  (implies (and (equal n (+ 1 end))
                (< end (len lst)) ;BOZO new
                (<= start end)
                (<= 0 start)
                (force (integerp end))
                (force (integerp start))
                (force (true-listp lst)))
           (perm (append (nthcdr n lst) (subrange start end lst))
                 (nthcdr (+ n -1 (- start end)) lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use (:instance append-subrange-nthcdr)
           :in-theory (disable append-subrange-nthcdr
                               equal-of-append))))


;; (thm
;;  (implies (and (equal k (+ 1 j))
;;                (<= i j)
;;                (natp i)
;;                (natp j)
;;                (natp k)
;;                (< j (len lst)))
;;           (perm (APPEND (NTHCDR k lst) (SUBRANGE i j lst))
;;                      (nthcdr i lst))))

;; ;move
;; (defthmd nth-with-large-index-2
;;   (implies (and (<= (len l) n)
;;                 (syntaxp (not (and (consp n)
;;                                    (equal (car n) 'quote)
;;                                    (equal (cadr n) '0)))))
;;            (equal (nth n l)
;;                   (if (zp n)
;;                       (nth 0 l)
;;                     nil)))
;;   :hints (("Goal" :in-theory (enable nth))))

;disabled since this introduces perm
(defthmd memberp-nth-when-perm
  (implies (and (perm lst1 lst2)
                (<= 0 n);
                (< n (len lst1))
                (integerp n))
           (memberp (nth n lst1) lst2)))

;bozo naming of LIST::APPEND-OF-NON-CONSP-2 vs. LIST::APPEND-OF-NON-CONSP-one

;(in-theory (disable NTH-WHEN-N-IS-ZP)) ;trying...

;(in-theory (disable PERM-OF-CONS)) ;trying...
;(in-theory (disable PERM-OF-CONS-MEMBERP-CASE))

(defthm cons-nth-onto-nthcdr
  (implies (and (equal n+1 (+ 1 n))
                (integerp n)
                (<= 0 n)
                (< n (len lst))
                )
           (equal (cons (nth n lst) (nthcdr n+1 lst))
                  (nthcdr n lst)))
  :hints (("Goal" :in-theory (enable nthcdr))))

;(in-theory (disable nthcdr-update-nth))

(defthm subrange-of-update-nth-irrel-1
  (implies (and (< (nfix n) start) ;this case
;                (<= 0 start)
                (integerp start)
                (integerp end) ;new
;                (<= start end)
                )
           (equal (subrange start end (update-nth n val lst))
                  (subrange start end lst)))
  :hints (("Goal" :in-theory (enable update-nth-rewrite subrange))))

;bozo gen
(defthm subsetp-equal-of-nthcdr-and-nthcdr
  (implies (and (integerp start)
                (< start (len lst)))
           (subsetp-equal (nthcdr (+ 1 start) lst)
                         (nthcdr start lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (nthcdr) (;CANCEL_PLUS-LESSP-CORRECT
                                     )))))

(defthm subsetp-equal-of-subranges-hack
  (implies (and (< end (len lst))
                (integerp start)
                (integerp end)
                (<= start end)
                (<= 0 start)
    ;               (<= 0 k)
                )
           (subsetp-equal (SUBRANGE (+ 1 ;k
                                      start) end lst)
                         (SUBRANGE start end lst))
           )
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (subrange take-of-nthcdr) (nthcdr-of-take)))))

(defthm cons-nth-onto-nthcdr-alt
  (implies (consp lst)
           (equal (cons (car lst) (nthcdr 1 lst))
                  lst))
  :hints (("Goal" :in-theory (e/d (nthcdr) (cons-nth-onto-nthcdr))
           :use (:instance cons-nth-onto-nthcdr (n 0) (n+1 1))
           )))

;gross because it introduces perm
(defthmd len-less-than-2-rewrite
 (equal (< (len lst) 2)
        (or (endp lst)
            (perm lst (list (car lst))))))

;use polarity here?
;this just seems bad
(defthmd len-less-than-2-rewrite-alt
  (implies (true-listp lst)
           (equal (< (LEN LST) 2)
                  (or (endp lst)
                      (equal lst (list (car lst)))))))

;; (defthm subsetp-equal-of-singleton
;;   (implies (and (not (consp (cdr lst2)))
;;                 (consp lst2)
;;                 (true-listp lst1)
;;                 )
;;            (equal (subsetp-equal lst1 lst2)
;;                   (or (endp lst1)
;;                       (equal lst1 (list (car lst2)))
;;                       )))
;;   :hints (("Goal"
;;            :in-theory (e/d (SUBSETP-EQUAL) (;SUBSETP-EQUAL-CDR-REMOVE-1-REWRITE
;;                                             )))))

;; (defthm subsetp-equal-of-singleton-alt
;;  (implies (and (consp lst2)
;; ;               (true-listp lst1)
;;                (not (consp (cdr lst2))))
;;           (equal (SUBSETP-EQUAL LST1 LST2)
;;                  (or (endp lst1)
;;                      (perm lst1 (list (car lst2)))
;;                     ; (equal lst1 (list (car lst2)))
;;                      )))
;;  :hints (("Goal" :expand ((SUBSETP-EQUAL (CDR LST1) LST2))
;;           :in-theory (e/d (SUBSETP-EQUAL) (;SUBSETP-EQUAL-CDR-REMOVE-1-REWRITE
;;                                                   )))))

(defthm perm-with-singleton-of-own-car
  (equal (PERM LST (LIST (CAR LST)))
         (equal 1 (len lst))))

(defthm memberp-car-of-take
  (equal (memberp (car lst) (take n lst))
         (and (integerp n)
              (< 0 n)))
  :hints (("Goal" :in-theory (enable take))))

(defthm memberp-nth-take
  (implies (and (< m n)
                (< n (len lst))
                (integerp m)
                (integerp n)
                (<= 0 m))
           (MEMBERP (nth m lst) (TAKE n lst)))
  :hints (("Goal" :in-theory (enable take nth))))

;; (defthm subsetp-equal-of-take-and-take
;;   (implies (and (<= m n)
;;                 (integerp n)
;;                 )
;;            (subsetp-equal (take m lst) (take n lst)))
;;   :hints (("Goal" :in-theory (enable take))))

;bozo gen
(defthm subsetp-equal-subrange-take
  (implies (and (< n2 n)
                (integerp m) ;new
                (integerp n)
                (integerp n2)
                )
           (subsetp-equal (SUBRANGE m n2 lst) (TAKE n lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (subrange ;take
                            TAKE-OF-NTHCDR
                            )
                           (NTHCDR-OF-TAKE)))))

;; (thm
;;  (IMPLIES (AND (NATP N)
;;                (< N END)
;;                (INTEGERP END)
;;                (< END (LEN LST))
;;                (CONSP LST)
;;                (<= N END)

;;           (MEMBERP (NTH N LST)
;;                          (NTHCDR N (TAKE END LST))))
;;  )

(defthm memberp-nth-of-subrange
  (implies (and (<= start n)
                (<= n end)
                (< end (len lst))
                (natp n)
                (natp end)
                (natp start)
                )
           (memberp (nth n lst) (subrange start end lst)))
  :hints (("Goal" :use (:instance NTH-OF-SUBRANGE (n (- n start)))
           :do-not-induct t
           :in-theory (disable NTH-OF-SUBRANGE))))

(defthm memberp-nth-of-nthcdr
  (implies (and (<= start n)
                (<= n (+ -1 (len lst)))
                (natp n)
                (natp start)
                )
           (memberp (nth n lst) (nthcdr start lst)))
  :hints (("Goal" :use (:instance memberp-nth-of-subrange (end (+ -1 (len lst)))
                                  (n n))
           :do-not-induct t
           :in-theory (disable memberp-nth-of-subrange))))



;; start of stuff for insertion sort...

(defthmd cons-nth-onto-take
 (implies (and (natp n)
               (< n (len lst)))
          (perm (cons (nth n lst) (take n lst))
                     (take (+ 1 n) lst)))
 :hints (("Goal" :in-theory (enable take))))


;bozo gen?
;i hope this is okay, since the presence of cdr means we're not in the nice nth/update-nth world any more.
(defthm update-nth-0-cdr
  (equal (update-nth 0 val (cdr lst))
         (cons val (cddr lst))))

(defthm cons-nth-1-onto-cddr
  (implies (<= 2 (len x))
           (equal (cons (NTH 1 x) (CDDR x))
                  (cdr x))))

;gen the 1
(defthm nth1-when-not-cdr
  (implies (NOT (CDR x))
           (equal (nth 1 x)
                  nil)))

;; (defthm perm-when-not-cdr
;;   (implies (not (cdr x))
;;            (equal (perm x y)
;;                   (if (consp x)
;;                       (list::equiv y (list (car x)))
;;                     (list::equiv y nil)
;;                     ))))

;; (defthm perm-when-not-cdr-alt
;;   (implies (not (cdr x))
;;            (equal (perm y x)
;;                   (if (consp x)
;;                       (list::equiv y (list (car x)))
;;                     (list::equiv y nil)
;;                     )))
;;   :hints (("Goal" :cases ((equal (len x) 1)))))

;drop?
(defthm cdr-non-nil
  (implies (< 1 (len x))
           (cdr x))
  :hints (("Goal" :expand ((LEN X)))))

;bozo drop?
(defthm unique-of-subrange-hack
  (implies (<= 3 (len lst))
           (equal (no-duplicatesp-equal (subrange 1 2 lst))
                  (not (equal (nth 1 lst)
                              (nth 2 lst)))))
  :hints (("Goal" :expand (take 3 lst)
           :in-theory (e/d (subrange take) (
                                                FIRSTN-OF-ONE-MORE ;bozo looped
                                                TAKE-OF-CDR
                                                3-cdrs
                                                )))))

;bozo add to bags lib
(defthm not-unique-of-cons-nth
  (implies (and (integerp n)
                (<= 0 n)
                (< n (len lst)))
           (not (NO-DUPLICATESP-EQUAL (CONS (NTH n LST) LST))))
  :hints (("Goal" :in-theory (enable NO-DUPLICATESP-EQUAL))))

(defthm car-equal-nth-when-unique-rewrite
  (implies (and (NO-DUPLICATESP-EQUAL lst)
                (<= 0 N)
                (integerp n)
                (< N (LEN lst)))
           (equal (EQUAL (CAR lst) (NTH N lst))
                  (EQUAL 0 n))))

(defthm car-not-memberp-of-cdr-when-unique
  (implies (and (consp lst)
                (no-duplicatesp-equal lst))
           (not (MEMBERP (CAR lst) (CDR lst))))
  :hints (("Goal" :in-theory (enable no-duplicatesp-equal))))

(defthm cons-nth-0-equal-self
  (equal (equal (cons (nth 0 x) y) x)
         (and (consp x)
              (equal y (cdr x)) ;bozo okay to introduce cdr?
              )))

;expensive
(defthmd cons-car-self-equal-self
  (implies (equal z (car x))
           (equal (equal (cons z y) x)
                  (and (consp x)
                       (equal y (cdr x)) ;bozo okay to introduce cdr?
                       ))))

;woohoo! this helped a lot
;rename? restrict to constants?
;compare to the rule below..
(defthm len-gives-consp
  (implies (and (equal (len x) k) ;reversed order Fri Dec 24 16:50:28 2010
                (< 0 k))
           (consp x)))

;this rule is for axe proofs only, due to how acl2 treats the second hyp
(defthm len-gives-consp-free
  (implies (and (equal k (len x)) ;acl2 will treat this hyp as a binding hyp and rewrite (len x)
                (< 0 k))
           (consp x))
  :rule-classes nil)

(defthmd update-nth-equal-cons-same
  (equal (equal (update-nth 0 val lst) (cons val rest))
         (equal (cdr lst) rest)))

(defthm update-nth-with-last-val
  (implies (and (syntaxp (and (quotep n)))
                (equal (+ n 1) (len lst))
                (true-listp lst)
                (natp n))
           (equal (update-nth n val lst)
                  (append (take n lst) (list val))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 1 nil nil)))
  :hints (("Goal" :in-theory (enable equal-of-append))))

(defthmd update-nth-of-0
  (implies (true-listp lst)
           (equal (update-nth 0 val lst)
                  (cons val (cdr lst)))))

;enable?
(defthmd 3-conses
  (implies (syntaxp (and (quotep a)
                         (quotep b)
                         (quotep c)))
           (equal (cons a (cons b (cons c lst)))
                  (append (list a b c) lst)))
  :hints (("Goal" :in-theory (enable take))))

(DEFTHM APPEND-OF-CONS-better
  (implies (syntaxp (not (and (quotep x)
                              (quotep a))))
           (EQUAL (APPEND (CONS A X) Y)
                  (CONS A (APPEND X Y)))))

(defthm subrange-when-too-far
  (implies (and (<= (len l) start)
                (natp start)
                (natp end))
           (equal (SUBRANGE start end L)
                  (repeat (+ 1 end (- start)) nil)))
  :hints (("Goal" :in-theory (e/d (SUBRANGE take nthcdr-of-cdr-combine) ()))))

;seems expensive
(defthmd nth-non-nil-rule
  (implies (and (nth n x)
                (natp n))
           (< n (len x)))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm nth-with-large-index-cheap
   (implies (and (not (< n (len x)))
                 (natp n))
            (not (nth n x)))
   :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

;(theory-invariant (incompatible (:rewrite LIST::LEN-POS-REWRITE) (:rewrite consp-cdr)))

;(local (in-theory (disable CANCEL_PLUS-LESSP-CORRECT))) ;why did this loop?

(defthm memberp-of-reverse-list
  (equal (memberp a (reverse-list lst))
         (memberp a lst))
  :hints (("Goal" :in-theory (enable REVERSE-LIST))))

;; (defthmd nth-when-l-is-not-a-consp-cheap
;;   (implies (not (consp l))
;;            (equal (nth n l) nil))
;;   :rule-classes ((:rewrite :backchain-limit-lst (1)))
;;   :hints (("Goal" :in-theory (enable nth))))

;special case for nth of nil?

(defthm perm-reverse-list
  (perm (reverse-list lst) lst)
  :hints (("Goal" :in-theory (enable reverse-list))))

;; (defthm nthcdr-of-len-same
;;   (equal (nthcdr (len x) x)
;;          (list::finalcdr x)))

;; (defthm equal-of-nil-and-finalcdr
;;   (equal (equal nil (list::finalcdr x))
;;          (true-listp x)))

(defthm not-of-nthcdr
  (implies (true-listp x)
           (equal (not (nthcdr n x))
                  (<= (len x) (nfix n)))))

(defthm equal-of-take-same
  (equal (equal x (take n x))
         (and (true-listp x)
              (equal (nfix n) (len x))))
  :hints (("Goal" :in-theory (enable take))))

;add to lists book
(defthm nthcdr-of-take-same
  (equal (nthcdr n (take n x))
         nil)
  :hints (("Goal" :in-theory (enable nthcdr-of-take))))

;; (DEFTHM LIST::EQUAL-APPEND-REDUCTION!-alt
;;   (EQUAL (EQUAL Z (APPEND X Y))
;;          (AND (LIST::EQUIV X (FIRSTN (LEN X) Z))
;;               (EQUAL Y (NTHCDR (LEN X) Z))))
;;   :hints (("Goal" :in-theory (enable LIST::EQUAL-APPEND-REDUCTION!))))

(in-theory (disable len)) ;new

;add to lists
(defthm len-of-update-nth-last-val
  (equal (len (update-nth (len lst) val lst))
         (+ 1 (len lst)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm update-nth-len-lst-becomes-append
  (equal (update-nth (len lst) val lst)
         (append lst (list val)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthmd update-nth-len-lst-becomes-append-strong
  (implies (equal n (len lst))
           (equal (update-nth n val lst)
                  (append lst (list val)))))

;BOZO don't unify with constants??
(defthm cons-equal-no-split
  (equal (equal (cons a rest1) (cons a rest2))
         (equal rest1 rest2)))

;; (defthm take-of-finalcdr
;;   (equal (take n (list::finalcdr x))
;;          (take n nil))
;;   :hints (("Goal" :in-theory (enable take))))

;dup?
;slow?
(defthm true-listp-when-not-consp
  (implies (not (consp lst))
           (equal (true-listp lst)
                  (equal nil lst)))
  :hints (("Goal" :in-theory (enable true-listp))))

;move
(defthm not-memberp-of-take2
  (implies (and (not (memberp a lst))
                (or (<= n (len lst))
                    (not (equal a nil))))
           (not (memberp a (take n lst))))
  :hints (("Goal" :in-theory (enable take))))

;; (defun sub1-sub1-cdr-induct (m n lst)
;;   (if (zp n)
;;       (list m n lst)
;;     (sub1-sub1-cdr-induct (+ -1 m) (+ -1 n) (cdr lst))))

(defthm equal-of-constant-and-repeat
  (implies (syntaxp (quotep k))
           (equal (equal k (repeat n val))
                  (if (zp n)
                      (equal k nil)
                    (and (all-same k) ;gets evaluated
                         (true-listp k)
                         (equal n (len k))
                         (equal val (car k))))))
  :hints (("Goal" :in-theory (e/d (all-equal$ repeat all-equal$-when-true-listp)
                                  (cons-onto-repeat equal-of-repeat-of-len-same)))))

;gross?
(defthmd append-of-take-and-cons-when-nth
  (implies (and (equal y (nth n x))
                (natp n))
           (equal (append (take n x) (cons y z))
                  (append (take (+ 1 n) x) z)))
  :hints (("Goal" :in-theory (enable equal-of-append))))

;gross?
(defthmd append-of-firstn-and-cons-when-nth
  (implies (and (equal y (nth n x))
                (< n (len x))
                (natp n))
           (equal (append (firstn n x) (cons y z))
                  (append (firstn (+ 1 n) x) z)))
  :hints (("Goal" :in-theory (enable equal-of-append))))

(defthm append-of-firstn-of-cons-of-nth
  (implies (and (natp n)
                (<= (+ 1 n) (len x)))
           (equal (append (firstn n x) (cons (nth n x) y))
                  (append (firstn (+ 1 n) x) y)))
  :hints (("Goal" :in-theory (enable equal-of-append))))

(defthm append-of-firstn-and-subrange
  (implies (and (< n (len x))
                (natp n)
                (<= m n)
                (natp m))
           (equal (append (firstn m x) (subrange m n x))
                  (firstn (+ 1 n) x)))
  :hints (("Goal" :in-theory (enable subrange equal-of-append))))

;; (defthm append-of-final-cdr-arg1
;;   (equal (append (LIST::FINALCDR x) y)
;;          y))

(defthm equal-of-constant-and-cons
  (implies (syntaxp (quotep k))
           (equal (equal k (cons x 'nil)) ;gen the nil?
                  (and (consp k)
                       (equal (car k) x)
                       (equal (cdr k) nil)))))

;drop?
;; (defthmd <-of-len-and-negative-constant
;;   (implies (and (syntaxp (quotep k))
;;                 (< k 0))
;;            (equal (< k (len x))
;;                   t)))

(defthm items-have-len-of-firstn
  (implies (items-have-len n lst)
           (items-have-len n (firstn m lst)))
  :hints (("Goal" :in-theory (e/d (items-have-len firstn)
                                  (take-of-cdr-becomes-subrange
                                   firstn-becomes-take-gen)))))

(defthm items-have-len-of-subrange-hack-gen
  (implies (and (natp start)
                (natp end)
                (natp n)
                (<= start end)
                (< end (len lst))
                )
           (implies (items-have-len n lst)
                    (items-have-len n (subrange start end lst))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;           :induct (ind2 start end lst)
           :in-theory (e/d (subrange items-have-len)
                           (take-of-cdr-becomes-subrange)))))

;; ;bozo gen
;; (defthm items-have-len-of-subrange-hack-gen
;;   (implies (and ;(natp start)
;;                 ;(natp end)
;;                 (< 9 (len lst))
;;                 )
;;            (implies (items-have-len n lst)
;;                     (items-have-len n (subrange 1 9;start end
;;                                                 lst))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;           :induct (ind2 start end lst)
;;            :in-theory (e/d (subrange ITEMS-HAVE-LEN) ()))))

(defthm equal-of-nil-and-nthcdr
  (implies (true-listp x)
           (equal (equal nil (nthcdr n x))
                  (if (not (natp n))
                      (equal nil x)
                    (<= (len x) n))))
  :hints (("Goal" :in-theory (e/d (nthcdr) (NTHCDR-OF-CDR-COMBINE)))))

(defthm equal-of-nil-and-cdr
  (implies (true-listp x)
           (equal (equal nil (cdr x))
                  (<= (len x) 1)))
  :hints (("Goal" :in-theory (e/d (nthcdr) (NTHCDR-OF-CDR-COMBINE)))))

;limit?!
(defthmd <-of-0-and-len-when-consp
  (implies (consp x)
           (< 0 (len x))))

(defthm list-split
  (implies (and (natp n)
                (<= n (len x)))
           (equal x (append (take n x) (nthcdr n x))))
  :rule-classes nil)

(defthm equal-of-take-and-take-when-not-equal-of-subranges
  (implies (and (not (equal (subrange low high x)
                            (subrange low high y)))
                (natp low)
                (natp high)
                (natp n)
                (< high n)
                )
           (equal (equal (take n x) (take n y))
                  nil))
  :hints (("Goal"
           :in-theory (e/d (subrange take-of-nthcdr)
                           (take-of-cdr-becomes-subrange
                            nthcdr-of-take))
    ;:use ((:instance LIST-SPLIT (x x) (n low))
    ;     (:instance LIST-SPLIT (x y) (n low)))
           )))

(defthm cons-onto-subrange-of-1-same
  (implies (integerp k)
           (equal (cons (nth 0 x) (subrange 1 k x))
                  (if (posp k)
                      (take (+ 1 k) x)
                    (list (nth 0 x)))))
  :hints (("Goal" :in-theory (enable ;EQUAL-CONS-CASES2-BETTER
                              ))))

;what else?!
(deftheory anti-subrange '(cdr-of-take-becomes-subrange-better

                           take-of-cdr-becomes-subrange
                           nthcdr-of-take-becomes-subrange
                           )
  :redundant-okp t)

;move
;rename: same start and end
(defthm subrange-of-update-subrange
  (implies (and (natp start)
                (natp end)
                (equal (+ 1 end (- start)) (len vals))
                (true-listp vals)
                (< end (len lst))
                )
           (equal (subrange start end (update-subrange start end vals lst))
                  vals))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (subrange ;update-subrange FIRSTN
                                     ) (anti-subrange)))))

(theory-invariant (incompatible (:rewrite UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF) (:rewrite UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF-back)))

(defthm update-subrange-when-no-third-piece
  (implies (and (<= (+ -1 (len lst)) end)
;                (<= start end)
                (true-listp lst) ;drop?
                (natp start)
                (natp end))
           (equal (update-subrange start end vals lst)
                  (if (<= start end)
                      (append (take start lst)
                              (take (+ 1 end (- start)) vals))
                    lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct t
           :in-theory (enable nth-when-n-is-zp
                              update-subrange
                              take
                              cdr-of-nthcdr
                              equal-cons-cases2
                              equal-of-append))))

;for Axe proofs - shouldn't we open endp?
;drop?
;; (defthm endp-of-cons
;;   (equal (endp (cons a x))
;;          nil))

(defthmd binary-append-opener
  (implies (consp x)
           (equal (binary-append x y)
                  (cons (car x)
                        (binary-append (cdr x) y)))))

(defthm len-of-update-nth-rewrite-2
  (implies (and (< n (len lst)) ;is this hyp ok?
                (natp n))
           (equal (len (update-nth n v lst))
                  (len lst))))

(defun indhh4 (lst n)
  (if (endp lst)
      (list lst n)
    (indhh4 (cdr lst) (+ -1 n))))

;(theory-invariant (incompatible (:rewrite LIST::FIX-OF-NTHCDR) (:rewrite NTHCDR-OF-TRUE-LIST-FIX)))

;TODO: Change the test to (consp (cdr x))?
(defthmd last-of-cdr-when-len-more-than-1
  (implies (< 1 (len lst)) ;other case?
           (equal (last (cdr lst))
                  (last lst)))
  :hints (("Goal" :induct t
           :in-theory (enable last))))

(defthm nth-of-0-and-last
  (implies (< 0 (len lst))
           (equal (nth 0 (last lst))
                  (nth (+ -1 (len lst)) lst)))
  :hints (("Goal" :induct t
           :expand ((last lst))
           :in-theory (e/d (last) (last-of-cdr)))))

(defthm subrange-of-reverse-list
  (implies (and (natp low)
                (<= low high)
                (< high (len lst))
                (natp high))
           (equal (subrange low high (reverse-list lst))
                  (reverse-list (subrange (+ -1 (len lst) (- high))
                                             (+ -1 (len lst) (- low))
                                             lst))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (subrange reverse-list nthcdr-of-true-list-fix)
                           (take-of-cdr-becomes-subrange)))))

(defthm subrange-too-far
  (implies (equal low (len x))
           (equal (subrange low high x)
                  (repeat (+ high 1 (- low)) nil)
                  ))
  :rule-classes ((:rewrite :backchain-limit-lst (1 ;nil
                                                 )))
  :hints (("Goal" :in-theory (e/d (subrange take) (anti-subrange)))))

(defthm append-take-nthcdr
  (implies (and (natp n)
                (true-listp l))
           (equal (append (take n l)
                          (nthcdr n l))
                  (append l
                          (repeat (- n (len l)) nil))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :in-theory (enable equal-of-append))))

(theory-invariant (incompatible (:rewrite CAR-BECOMES-NTH-OF-0) (:rewrite NTH-WHEN-N-IS-ZP)))

;maybe only do this in the conclusion?
;disabled since i've seen this be involved in loops
(defthmd equal-rewrite-when-takes-equal
  (implies (and (equal (take n x) (take n y)) ;binds the free variable n
                (true-listp x)
                (true-listp y)
                (< n (len x))
                (< n (len y))
                (natp n))
           (equal (EQUAL x y)
                  (EQUAL (nthcdr n x) (nthcdr n y))))
  :hints (("Goal" :use ((:instance APPEND-take-NTHCDR (l x))
                        (:instance APPEND-take-NTHCDR (l y))
                        )
           :in-theory (disable append-take-nthcdr
                               equal-of-append))))

(defthm equal-of-firstn-and-firstn-when-equal-of-nthcdr-and-nthcdr
  (implies (and (equal (nthcdr n x) (nthcdr n y))
                (natp n)
                (true-listp x)
                (true-listp y))
           (equal (equal (firstn n x) (firstn n y))
                  (equal x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil)))
  :hints (("Goal" :use ((:instance APPEND-take-NTHCDR (l x))
                        (:instance APPEND-take-NTHCDR (l y)))
           :in-theory (disable APPEND-take-NTHCDR
                               equal-of-append
                               ))))

(defthm equal-of-take-and-take-when-equal-of-nthcdr-and-nthcdr
  (implies (and (equal (nthcdr n x) (nthcdr n y))
                (natp n)
                (<= n (len x))
                (<= n (len y))
                (true-listp x)
                (true-listp y))
           (equal (equal (take n x) (take n y))
                  (equal x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil nil nil)))
  :hints (("Goal" :use ((:instance append-take-nthcdr (l x))
                        (:instance APPEND-TAKE-NTHCDR (l y)))
           :in-theory (disable APPEND-TAKE-NTHCDR
                               equal-of-append
                               ))))

(theory-invariant (incompatible (:rewrite NTHCDR-OF-CDR-COMBINE-STRONG) (:definition nthcdr)))

(defthm equal-of-nthcdr-and-nthcdr
  (implies (and (natp start1)
                (<= start1 (len lst))
                (<= start2 (len lst))
                (natp start2))
           (equal (equal (nthcdr start1 lst) (nthcdr start2 lst))
                  (equal start1 start2)))
  :hints (("Goal" :in-theory (e/d (nthcdr cdr-of-nthcdr) (nthcdr-of-cdr-combine NTHCDR-OF-CDR-COMBINE-STRONG)))))

(defthm equal-of-subrange-and-subrange-same-lsts-and-ends
  (implies (and (natp start1)
                (natp start2)
                (natp end))
           (equal (equal (subrange start1 end lst) (subrange start2 end lst))
                  (if (< end start1)
                      (< end start2)
                    (equal start1 start2))))
  :hints (("Goal"
           :use ((:instance SUBRANGE-OUT-OF-ORDER (start start1))
                 (:instance SUBRANGE-OUT-OF-ORDER (start start2)))
           :in-theory (e/d (subrange) (
                                       TAKE-OF-CDR-BECOMES-SUBRANGE

                                       nthcdr-of-take)))))


;the regular rule, len-of-subrange, gives rise to ifs during backchaining
;this covers the usual case...
(defthm len-of-subrange2
  (implies (and (<= start end)
                (<= 0 start)
                (< end (len lst))
                (integerp end)
                (integerp start)
                )
           (equal (len (subrange start end lst))
                  (+ 1 end (- start)))))

;rename
(defthm subrange-split-top
  (implies (and (natp i)
                (<= low i)
                (natp low)
                (< i (len x)))
           (equal (append (subrange low (+ -1 i) x) (list (nth i x)))
                  (subrange low i x))))

(defthmd take-split
  (implies (and (natp n)
                (< 0 n)
                (< n (len x))
                )
           (equal (take n x)
                  (append (take (+ -1 n) x) (list (nth (+ -1 n) x)))))
  :hints (("Goal" :in-theory (enable equal-of-append))))

(defthm update-nth-add-onto-end
  (implies (true-listp lst)
           (equal (update-nth (len lst) val lst)
                  (append lst (cons val nil)))))

(defthm cons-nth-1-onto-cddr-better
  (equal (cons (nth 1 x) (cddr x))
         (if (<= 2 (len x))
             (cdr x)
           (cons (nth 1 x) nil))))

(defthm cons-nth-0-onto-cdr-better
  (equal (cons (nth 0 x) (cdr x))
         (if (<= 1 (len x))
             x
           (cons (nth 0 x) nil))))


;rename
(defthm cons-nth-0-nth-1
  (implies (true-listp x)
           (equal (list (nth 0 x) (nth 1 x))
                  (if (equal 0 (len x))
                      (list nil nil)
                    (if (equal 1 (len x))
                        (list (car x) nil)
                      (take 2 x)))))
  :hints (("Goal" :in-theory (enable equal-cons-cases2))))

(defthm len-of-if
  (equal (len (if test x y))
         (if test (len x) (len y))))

(defthm subrange-of-nthcdr
  (implies (and (natp n)
                (natp start)
                (natp end))
           (equal (subrange start end (nthcdr n x))
                  (subrange (+ start n) (+ end n) x)))
  :hints (("Goal" :in-theory (e/d (subrange take-of-nthcdr)
                                  (nthcdr-of-take anti-subrange)))))

;rename?
(defthmd subrange-rewrite
  (implies (and (not (< end start))
                (natp end)
                (natp start))
           (equal (subrange start end lst)
                  (cons (nth start lst)
                        (subrange (+ 1 start) end lst))))
  :hints (("Goal" :in-theory (e/d (SUBRANGE CDR-OF-NTHCDR EQUAL-CONS-CASES2)
                                  (anti-subrange)))))

(defthm subrange-of-UPDATE-SUBRANGE-irrel
  (implies (and (< k m1)
                (<= m2 (len lst))
                (<= k (len lst))
                (natp n)
                (natp m1)
                (natp m2)
                (natp k)
                )
           (equal (SUBRANGE N k (UPDATE-SUBRANGE m1 m2 VALS LST))
                  (SUBRANGE N k LST)))
  :hints (("Goal" :in-theory (e/d (SUBRANGE UPDATE-SUBRANGE)
                                  (anti-subrange UPDATE-NTH-OF-UPDATE-SUBRANGE UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

(defthm subrange-of-update-subrange-last-portion
  (implies (and (equal (len vals) (+ 1 (- k low)))
                (< k (len lst))
                (<= n low)
                (natp n)
                (natp low)
                (natp k)
                )
           (equal (SUBRANGE n k (UPDATE-SUBRANGE low k vals lst))
                  (append (SUBRANGE n (+ -1 low) lst) (true-list-fix vals))))
  :hints (("Goal" :in-theory (e/d (SUBRANGE)
                                  (anti-subrange UPDATE-NTH-OF-UPDATE-SUBRANGE UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

;bozo prove this without opening up subrange?
;bozo gen
(defthm subrange-of-update-subrange-all-cases
  (implies (and (equal (len vals) (+ end2 (- start2) 1))
                (<= start end)
                (<= start2 end2)
                (< end (len lst))
                (< end2 (len lst))
                (natp start)
                (natp start2)
                (natp end)
                (natp end2)
                (true-listp lst)
                (true-listp vals)
;               (not (< end start2))
;               (not (< start start2))
;               (not (<= end end2))
;               (<= start end2)
                )
           (equal (subrange start end (update-subrange start2 end2 vals lst))
                  (if (< end start2)
                      (subrange start end lst)
                    (if (< start start2)
                        (if (< end end2)
                            (append (subrange start (+ -1 start2) lst)
                                    (take (+ 1 (- end start2)) vals))
                          (append (subrange start (+ -1 start2) lst)
                                  (take (+ 1 (- end2 start2)) vals)
                                  (SUBRANGE (+ 1 END2) END LST)))
                      (if (<= end end2)
                          (subrange (- start start2)
                                    (- end start2)
                                    vals)
                        (if (<= start end2)
                            (append (subrange (- start start2) (- end2 start2) vals)
                                    (subrange (+ 1 end2) end lst))
                          (subrange start end lst)
                          ))))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :do-not-induct t
;          :expand (update-subrange start2 end2 vals lst)
           :in-theory (e/d (subrange nth-when-n-is-zp
                            update-subrange-rewrite)
                           (anti-subrange
                            update-nth-of-update-subrange     ;bozo
                            update-nth-of-update-subrange-diff ;bozo
                            )))))

;; (defthm update-subrange-equiv
;;   (implies (and (equal (len vals) (+ end (- start) 1))
;;                 (<= start end)
;;                 (< end (len lst))
;;                 (natp start)
;;                 (natp end)
;;                 (true-listp lst)
;;                 (true-listp vals)
;;                 )
;;            (list::equiv (UPDATE-SUBRANGE start end vals lst)
;;                         (append (take start lst)
;;                                 vals
;;                                 (nthcdr (+ 1 end) lst))))
;;   :hints (("Goal" :in-theory (e/d (subrange
;;                                    update-subrange-rewrite)
;;                                   (anti-subrange
;;                                    update-nth-of-update-subrange     ;bozo
;;                                    update-nth-of-update-subrange-diff ;bozo
;;                                    )))))

;do we need priorities here?
;can loop with EQUAL-OF-NIL-WHEN-TRUE-LISTP...
(defthmd equal-of-0-and-len-when-true-listp
  (implies (true-listp x)
           (equal (equal 0 (len x))
                  (equal nil x))))

;; (defthm finalcdr-iff
;;   (iff (list::finalcdr x)
;;        (not (true-listp x)))
;;   :hints (("Goal" :in-theory (enable true-listp list::finalcdr))))

(defthm append-of-constant-and-cons-of-constant
  (implies (syntaxp (and (quotep x)
                         (quotep a)))
           (equal (append x (cons a b))
                  (append (append x (list a))
                          b))))

(defthm equal-of-append-of-cons-and-append-cancel
  (implies (true-listp z)
           (equal (equal (append x (cons a y)) (append z y))
                  (equal (true-list-fix z) (append x (list a)))))
  :hints (("Goal" :use (:instance equal-of-append-and-append-same-arg2
                                  (x1 (append x (list a)))
                                  (x2 z))
           :in-theory (disable equal-of-append-and-append-same-arg2))))



;seems pretty special purpose...
(defthm cons-nth-reverse-list-take
  (implies (and (natp n)
                (< n (len lst)))
           (equal (cons (nth n lst) (reverse-list (take n lst)))
                  (reverse-list (take (+ 1 n) lst))))
  :hints (("Goal" :in-theory (e/d (reverse-list take) (TAKE-OF-CDR-BECOMES-SUBRANGE)))))

;; (defthm len-of-finalcdr
;;   (equal (len (list::finalcdr x))
;;          0))

(defthm subrange-of-update-nth-start
  (implies (and; (< end (len lst))
                (<= start end)
                (natp start)
                (natp end))
           (equal (subrange start end (update-nth start val lst))
                  (cons val (subrange (+ 1 start) end lst))))
  :hints (("Goal" ;:cases ((<= start end))
           :in-theory (enable equal-cons-cases2 len-update-nth))))

;move
(defthm subrange-of-subrange
  (implies (and (< end1 (+ 1 end2 (- start2)))
                (natp start1)
                (natp start2)
                (natp end1)
                (natp end2))
           (equal (subrange start1 end1 (subrange start2 end2 lst))
                  (subrange (+ start1 start2) (+ start2 end1) lst)))
  :hints (("Goal" :in-theory (e/d (subrange)
                                  (anti-subrange)))))

;trying... since this caused case splits when we couldn't always resolve the length of the args (since they came from table lookups)
;(in-theory (disable list::nth-append))

(defthm nth-append-1
  (implies (< (nfix n) (len a))
           (equal (nth n (append a b))
                  (nth n a))))

(defthm nth-append-2
  (implies (not (< (nfix n) (len a)))
           (equal (nth n (append a b))
                  (nth (- (nfix n) (len a)) b))))

;follows from UNIQUE-OF-CONS-NO-SPLIT but this is a "simple" rule (i.e., an abbreviation rule)
(defthm no-duplicatesp-equal-of-singleton
  (no-duplicatesp-equal (cons x nil)))

;bozo gen
(defthm subrange-of-update-nth-end-of-range
  (IMPLIES (AND (NATP START)
                (natp end)
                (<= start end)
                (< end (len lst)))
           (EQUAL (SUBRANGE START end (UPDATE-NTH end VAL LST))
                  (append (SUBRANGE START (+ -1 end) LST)
                          (list val))))
  :hints (("Goal" :in-theory (e/d (SUBRANGE) (anti-subrange)))))

(defthm subrange-of-update-nth-irrel-2
  (implies (and (< end (nfix n)) ;this case
                (integerp start))
           (equal (subrange start end (update-nth n val lst))
                  (subrange start end lst)))
  :hints (("Goal" :in-theory (e/d (take update-nth-rewrite subrange)
                                  (TAKE-OF-CDR-BECOMES-SUBRANGE)))))

;; (defun indh2 (n m)
;;   (if (zp m)
;;       (list n m)
;;     (indh2 (+ -1 n) (+ -1 m))))

;; (thm
;;  (implies (<= (nfix n) (nfix m))
;;           (equal (TAKE n (REPEAT m val))
;;                  (repeat n val)))
;;  :hints (("Goal" :in-theory (e/d (;take
;;                                   repeat)
;;                                  (anti-subrange
;;                                   LIST::EQUAL-REPEAT-CONS)))))

(defthm subrange-of-update-nth-contained
  (implies (and (<= (nfix n) end)
                (<= start (nfix n))
                (integerp end)
                (natp start))
           (equal (subrange start end (update-nth n val lst))
                  (update-nth (- n start) val (subrange start end lst))))
  :hints (("Goal" :in-theory (e/d (take update-nth-rewrite subrange nthcdr-of-cdr-combine)
                                  (TAKE-OF-CDR-BECOMES-SUBRANGE)))))

;covers all three cases:
(defthm subrange-of-update-nth
  (implies (and (integerp end)
                (natp start))
           (equal (subrange start end (update-nth n val lst))
                  (if (< end (nfix n))
                      (subrange start end lst)
                    (if (< (nfix n) start)
                        (subrange start end lst)
                      (update-nth (- n start) val (subrange start end lst)))))))

(defthm update-subrange2-all
  (implies (and (equal len-1 (+ -1 len))
                (natp len)
        ;        (true-listp lst) ;drop?
                )
           (equal (update-subrange2 len 0 len-1 vals lst)
                  (take len vals)))
  :hints (("Goal" :cases ((equal 0 len))
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable update-subrange2))))

;; (defthm consp-of-finalcdr
;;   (equal (CONSP (LIST::FINALCDR PARAMS))
;;          nil))

(defthm equal-of-cons-of-nth-0-same
  (equal (equal x (cons (nth 0 x) rest))
         (and (< 0 (len x))
              (equal (nthcdr 1 x) rest))))

(defthm equal-of-nthcdr-and-nth-same
  (implies (natp n)
           (equal (equal (nthcdr n x) (cons (nth n x) rest))
                  (and (consp (nthcdr n x))
                       (equal (nthcdr (+ 1 n) x) rest))))
  :hints (("Goal" :in-theory (enable cdr-of-nthcdr))))

(defthm equal-of-nthcdr-and-cons
  (implies (and (equal (nth n x) a)
                (natp n))
           (equal (equal (nthcdr n x) (cons a rest))
                  (and (consp (nthcdr n x))
                       (equal (nthcdr (+ 1 n) x) rest))))
  :rule-classes ((:rewrite :backchain-limit-lst (2 1))))

(defthm equal-of-cons-when-equal-nth-0-cheap
  (implies (equal (nth 0 x) a)
           (equal (equal x (cons a rest))
                  (and (consp x)
                       (equal (nthcdr 1 x) rest))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthmd equal-of-cons-when-equal-nth-0
  (implies (equal (nth 0 x) a)
           (equal (equal x (cons a rest))
                  (and (consp x)
                       (equal (nthcdr 1 x) rest))))
  :rule-classes ((:rewrite :backchain-limit-lst (2))))


(defthm equal-of-cdr-and-cons-of-nth-of-1
  (equal (equal (cdr x) (cons (nth 1 x) y))
         (and (< 1 (len x))
              (equal (cddr x) y)))
  :hints (("Goal" :in-theory (disable))))

(defthm equal-of-nthcdr-and-cons-of-nth
  (implies (natp n)
           (equal (equal (nthcdr n x) (cons (nth n x) y))
                  (and (< n (len x))
                       (equal (nthcdr (+ 1 n) x) y))))
  :hints (("Goal" :in-theory (disable))))

;(defmacro memberp (a x) `(memberp ,a ,x))

;BOZO get rid of takes?
(DEFTHM SUBRANGE-OF-UPDATE-SUBRANGE-ALL-CASES-better
  (IMPLIES
   (AND ; (EQUAL (LEN VALS) (+ END2 (- START2) 1))
    (<= START END)
    (<= START2 END2)
    (< END (LEN LST))
    (< END2 (LEN LST))
    (NATP START)
    (NATP START2)
    (integerp END)
    (NATP END2)
    (TRUE-LISTP LST)
    (TRUE-LISTP VALS))
   (EQUAL
    (SUBRANGE START END
              (UPDATE-SUBRANGE START2 END2 VALS LST))
    (IF (< END START2)
        (SUBRANGE START END LST)
        (IF (< START START2)
            (IF (< END END2)
                (APPEND (SUBRANGE START (+ -1 START2) LST)
                        (TAKE (+ 1 (- END START2)) (take (+ END2 (- START2) 1) vals)))
                (APPEND (SUBRANGE START (+ -1 START2) LST)
                        (TAKE (+ 1 (- END2 START2)) (take (+ END2 (- START2) 1) vals))
                        (SUBRANGE (+ 1 END2) END LST)))
            (IF (<= END END2)
                (SUBRANGE (- START START2)
                          (- END START2)
                          (take (+ END2 (- START2) 1) vals))
                (IF (<= START END2)
                    (APPEND (SUBRANGE (- START START2)
                                      (- END2 START2)
                                      (take (+ END2 (- START2) 1) vals))
                            (SUBRANGE (+ 1 END2) END LST))
                    (SUBRANGE START END LST)))))))
  :hints (("Goal" :use (:instance SUBRANGE-OF-UPDATE-SUBRANGE-ALL-CASES (vals (take (+ END2 (- START2) 1) vals)))
           :in-theory (e/d (TAKE-OF-CDR-BECOMES-SUBRANGE posp)
                           (SUBRANGE-OF-UPDATE-SUBRANGE-ALL-CASES)))))

;bozo gen?
(defthm update-nth-equal-update-subrange-special
  (implies (and (<= n end)
                (< end (len lst))
                (natp n)
                (natp end)
                (equal val1 val2)
                (equal lst1 (update-subrange (+ 1 n) end rst lst2))
                )
           (equal (equal (update-nth n val1 lst1)
                         (update-subrange n end (cons val2 rst) lst2))
                  t))
  :hints (("Goal" :in-theory (e/d (update-subrange) (update-nth-of-update-subrange-diff)))))

(defthm subrange-of-update-subrange-contained
  (implies (and (<= start2 start1)
                (<= end1 end2)
                (<= start1 end1)
                (<= start2 end2)
                (< end2 (len lst))
                (equal (len vals) (+ end2 1 (- start2)))
                (natp start1)
                (natp start2)
                (natp end1)
                (natp end2)
                )
           (equal (SUBRANGE start1 end1 (UPDATE-SUBRANGE start2 end2 vals lst))
                  (SUBRANGE (- start1 start2) (- end1 start2) vals)))
  :hints (("Goal" :in-theory (e/d (SUBRANGE) (;anti-subrange
                                              )))))

;bozo gen
(defthm subrange-of-update-subrange-not-quite-skew
  (implies (and (natp start)
                (<= start end)
                (< end (len lst))
                (natp end)
;;                 (equal (+ end (- start))
;;                        (len vals))
                )
           (equal (subrange start end (update-subrange (+ 1 start) end vals lst))
                  (cons (nth start lst)
                        (subrange 0 (+ end -1 (- start)) vals))))
  :hints (("Goal" :in-theory (e/d (update-subrange-rewrite
                                   ;EQUAL-CONS-CASES2
                                   SUBRANGE-OF-CONS
                                   )
                                  (;anti-subrange;
                                   ))
           :cases ((equal end (+ start 1)))
           :do-not '(generalize eliminate-destructors)
           :expand ((subrange start end
                              (update-subrange (+ 1 start)
                                               end vals
                                               lst))))))

(defthmd subrange-differs-hack
  (implies (and (not (equal (subrange start end lst1) ;binds start and end
                            lst2))
                (not (equal (subrange start end x)
                            (subrange start end y))))
           (equal (equal x y)
                  nil)))

;; (defthmd update-subrange-rewrite
;;   (implies (and
;;             (natp start)
;;             (natp end)
;;             (true-listp lst)
;;             (true-listp vals)
;;             (<= start end)
;;             (equal (+ 1 end (- start)) (len vals))
;;             (< end (len lst)))
;;            (equal (update-subrange start end vals lst)
;;                   (append (take start lst)
;;                           vals
;;                           (nthcdr (+ 1 end) lst))))
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm update-subrange-equal-rewrite
   (implies (and (equal (len lst1) (len lst2))
                 (natp start)
                 (natp end)
                 (true-listp lst1)
                 (true-listp lst2)
                 (true-listp vals)
                 (<= start end)
                 (equal (+ 1 end (- start)) (len vals))
                 (< end (len lst1))
    ;                (= start 2) (= end 5) (equal vals '(1 2 3 4)) (equal lst1 '(a b c d e f)) (equal lst2 '(aa bb cc dd ee ff))
                 )
            (equal (equal (update-subrange start end vals lst1) lst2)
                   (and (equal vals (subrange start end lst2))
                        (equal (take start lst1)
                               (take start lst2))
                        (equal (nthcdr (+ 1 end) lst1)
                               (nthcdr (+ 1 end) lst2)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (enable update-subrange-rewrite
                               equal-of-append
                               take-of-nthcdr-becomes-subrange))))

(DEFTHM TAKE-OF-UPDATE-SUBRANGE-LEMMA-better
  (IMPLIES
   (AND (<= N (+ 1 END))
        (< END (LEN LST))
;        (EQUAL (+ 1 END (- START)) (LEN VALS))
        (NATP START)
        (NATP END)
        (NATP N)
        (<= START N))
   (EQUAL (TAKE N (UPDATE-SUBRANGE START END VALS LST))
          (APPEND (TAKE START LST)
                  (TAKE (- N START) VALS))))
  :HINTS
  (("Goal" :DO-NOT '(GENERALIZE ELIMINATE-DESTRUCTORS)
    :IN-THEORY
    (E/D (;CONS-CAR-SELF-EQUAL-SELF
          TAKE UPDATE-SUBRANGE
          UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF-BACK)
         (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))


;drop?
(defthmd update-subrange-rewrite-better2
  (implies (and (< end (len lst))
                (natp start)
                (natp end)
                (<= start end))
           (equal (update-subrange start end vals lst)
                  (append (take start lst)
                          (take (+ 1 end (- start)) vals)
                          (nthcdr (+ 1 end) lst))))
  :hints (("Goal" :use (:instance update-subrange-rewrite
                                  (lst (true-list-fix lst))
                                  (vals (take (+ 1 end (- start)) vals)))
           :in-theory (e/d (nthcdr-of-true-list-fix equal-of-append)
                           (update-subrange-rewrite ;update-subrange-equiv
                            )))))

;; (DEFTHM UPDATE-SUBRANGE-when-extends
;;   (IMPLIES (AND (not (< END (LEN LST)))
;;                 (<= start end)
;;                 (NATP END)
;;                 (NATP START))
;;            (EQUAL (UPDATE-SUBRANGE START END VALS LST)
;;                   (UPDATE-SUBRANGE START END VALS (take (+ 1 end) LST))))
;;   :hints (("Goal" :in-theory (enable update-subrange-rewrite-better take-rewrite))))

;;   :HINTS
;;   (("Goal"
;;     :IN-THEORY
;;     (E/D
;;      (UPDATE-SUBRANGE UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF-BACK)
;;      (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

;; (DEFTHM LEN-OF-UPDATE-SUBRANGE-better
;;   (IMPLIES (AND (not (< END (LEN LST)))
;;                 (<= start end)
;;             (NATP END)
;;             (NATP START))
;;            (EQUAL (LEN (UPDATE-SUBRANGE START END VALS LST))
;;                   (+ 1 end)))
;;   :HINTS
;;   (("Goal"
;;     :IN-THEORY
;;     (E/D
;;      (UPDATE-SUBRANGE UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF-BACK)
;;      (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

;BOZO why so many cases?
;BOZO gen!
(defthm update-subrange-of-update-subrange-when-outer-is-one-smaller
  (implies (and; (equal (len vals) (- n start))
                (equal m (+ 1 start))
                (<= m n)
       ;         (< n (len lst))
 ;               (true-listp lst)
;                (true-listp vals)
                (natp start)
                (natp n)
                )
           (equal (update-subrange m n vals (update-subrange start n vals2 lst))
                  (update-subrange m n vals (update-nth start (nth 0 vals2) lst))))
  :hints (("Goal" :in-theory (enable update-subrange-rewrite-better equal-of-append))))

;; ;BOZO challenges:
;; (UPDATE-NTH
;;         4
;;         x
;;         (UPDATE-SUBRANGE
;;            3 6 vals
;;            (UPDATE-SUBRANGE
;;                 2 6 vals2 lst)))

(defthm update-nth-of-UPDATE-SUBRANGE-last
  (implies (and (equal (+ 1 n (- m)) (len vals))
                (natp m)
                (< m n)
                (true-listp vals)
                (true-listp lst)
                (natp n)
                (< n (len lst)))
           (equal (UPDATE-NTH n val (UPDATE-SUBRANGE m n vals lst))
                  (UPDATE-NTH n val (UPDATE-SUBRANGE m (- n 1) (take (- n m) vals) lst))))
  :hints (("Goal" :in-theory (enable UPDATE-SUBRANGE-REWRITE CDR-OF-NTHCDR equal-of-append))))

(defthm UPDATE-NTH-of-UPDATE-subrange-contained
  (implies (and (<= start n)
                (<= n end)
                (natp start)
                (natp end)
                (natp n))
           (equal (UPDATE-NTH n val (UPDATE-SUBRANGE start end vals lst))
                  (UPDATE-SUBRANGE start end (update-nth (- n start) val vals) lst)))
  :hints (("Goal" :in-theory (enable UPDATE-SUBRANGE-rewrite))))

;slow proof (many cases)
(defthm update-subrange-of-update-subrange-reorder
  (implies (and (< end2 start1)
                (natp start1)
                (natp start2)
                (natp end1)
                (natp end2))
           (equal (update-subrange start1 end1 vals1 (update-subrange start2 end2 vals2 lst))
                  (update-subrange start2 end2 vals2 (update-subrange start1 end1 vals1 lst))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (e/d (update-subrange-rewrite-better take-of-nthcdr-becomes-subrange)
                                  (equal-of-append
                                   natp
                                   ;; for speed:
                                   <-of-+-combine-constants-2)))))
