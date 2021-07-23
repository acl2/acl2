; Yet more material on addresses
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; "top" book about addresses (FIXME combine these books)

;(include-book "coi/records/defarray" :dir :system) ;to get the rkeys function (old comment?)
(include-book "adslemmas")
(include-book "ads2")
(include-book "kestrel/lists-light/firstn-def" :dir :system)
(include-book "kestrel/maps/maps" :dir :system)
(local (include-book "kestrel/lists-light/memberp" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/firstn" :dir :system))

(defthm g-of-new-ad
  (equal (g (new-ad (rkeys heap)) heap)
         nil))

;could be expensive?
(defthmd g-when-not-in-rkeys
  (implies (not (set::in key (rkeys rec)))
           (equal (g key rec)
                  nil)))

(defthmd g-of-nil-lemma
  (implies (equal x nil)
           (equal (g a x)
                  nil)))

(defthm s-iff-when-g
  (implies (and (g key2 map)
                (not (equal key key2)))
           (iff (s key val map)
                t))
  :hints (("Goal" :use ((:instance G-diff-S (b key) (r MAP) (a key2) (v val))
                        (:instance g-of-nil-lemma (a key2) (x (S KEY VAL MAP))))
           :in-theory (disable G-WHEN-NOT-IN-RKEYS G-IFF-GEN G-OF-NIL-IS-NIL)
           )))

(in-theory (disable NTH-NEW-AD2-COLLECT))

(local (in-theory (disable SET::PICK-A-POINT-SUBSET-STRATEGY SET::DOUBLE-CONTAINMENT)))
(local (in-theory (disable LIST::2SET
                           ;; LIST::MEMBER-EQ-IS-MEMBERP-PROPOSITIONALLY
                           ;; LIST::MEMBER-IS-MEMBERP-PROPOSITIONALLY
                           ;; LIST::MEMBER-equal-IS-MEMBERP-PROPOSITIONALLY
                           )))

;needs more hyps
;; (defthm NEW-ADS-SLICE-split
;;   (implies (and (natp low)
;;                 (natp mid)
;;                 (natp high))
;;            (equal (NEW-ADS-SLICE low high dom)
;;                   (APPEND (NEW-ADS-SLICE mid high dom) (NEW-ADS-SLICE low mid dom))


;; (skip-proofs
;;  (defthmd 2set-append-NEW-ADS-SLICE-NEW-ADS-SLICE
;;    (implies (and (natp low)
;;                  (natp mid)
;;                  (natp high))
;;             (equal (LIST::|2SET| (APPEND (NEW-ADS-SLICE mid high dom) (NEW-ADS-SLICE low mid dom)))
;;                    (LIST::|2SET| (NEW-ADS-SLICE low high dom))))
;;    :hints (("Goal" :in-theory (enable NEW-ADS-SLICE LIST::|2SET| N-NEW-ADS)))))

;; (skip-proofs
;;  (defthmd 2set-append-NEW-ADS-SLICE-NEW-ADS-SLICE-adjacent
;;    (implies (and (equal low1 (+ 1 high2))
;;                  (natp low1)
;;                  (natp high1)
;;                  (<= low1 high1)
;;                  (natp low2)
;;                  (natp high2)
;;                  (<= low2 high2))
;;             (equal (LIST::|2SET| (APPEND (NEW-ADS-SLICE low1 high1 dom) (NEW-ADS-SLICE low2 high2 dom)))
;;                    (LIST::|2SET| (NEW-ADS-SLICE low2 high1 dom))))
;;    :hints (("Goal" :in-theory (enable NEW-ADS-SLICE LIST::|2SET| N-NEW-ADS)))))

;; (skip-proofs
;;  (defthmd n-new-ads-becomes-n-new-ads2
;;    (equal (n-new-ads n dom)
;;           (n-new-ads2 n dom))))

(in-theory (disable n-new-ads-becomes-n-new-ads2))

(defthm nth-of-n-new-ads2
  (implies (and (natp n) (natp m) (< n m) (<= 0 n))
           (equal (nth n (n-new-ads2 m dom))
                  (nth-new-ad (+ 1 n) dom)))
  :hints (("Goal"
           :use (:instance nth-of-n-new-ads (ads dom))
           :in-theory (e/d (n-new-ads-becomes-n-new-ads2) (nth-of-n-new-ads)))))

(DEFTHM INSERT-NEW-AD-INSERT-2ND-NEW-ADalt
  (IMPLIES
   (SET::SETP DOM)
   (EQUAL (SET::INSERT (NTH-NEW-AD 2 DOM)
                       (SET::INSERT (NEW-AD DOM) DOM))
          (SET::UNION (LIST::|2SET| (N-NEW-ADS 2 DOM))
                      DOM))))

(DEFTHM IN-OF-NEW-AD-AND-N-NEW-ADS2-better
  (IMPLIES (AND (INTEGERP N) (< 0 N))
           (equal (MEMBERP (NEW-AD DOM)
                                 (N-new-ads2 N DOM))
                  t))
  :hints (("Goal" :in-theory (e/d (N-NEW-ADS-BECOMES-N-NEW-ADS2)( IN-OF-NEW-AD-AND-N-NEW-ADS IN-OF-NEW-AD-AND-N-NEW-ADS NEW-AD-NOT-MEMBERP-OF-NEW-ADS MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP NEW-AD-NOT-MEMBERP-OF-NEW-ADS-SLICE))
          :use (:instance IN-OF-NEW-AD-AND-N-NEW-ADS (ads dom))))
)


(DEFTHM
  NEW-AD-OF-UNION-DOM-AND-N-NEW-ADSalt
  (IMPLIES
   (AND (NATP N) (<= 0 N))
   (EQUAL
    (NEW-AD (SET::UNION (LIST::|2SET| (N-NEW-ADS N DOM)) DOM))
    (NTH-NEW-AD (+ 1 N) DOM)))
  :OTF-FLG T
  :HINTS
  (("Goal" :DO-NOT '(GENERALIZE ELIMINATE-DESTRUCTORS)
    :INDUCT (NTH-NEW-AD N DOM)
    :DO-NOT-INDUCT T
    :EXPAND ((N-NEW-ADS 1 DOM))
    :IN-THEORY
    (E/D ((:INDUCTION NTH-NEW-AD)
          N-NEW-ADS-AUX
          UNION-OF-2SET-AND-2SET-BACK)
         (NEW-ADS-SLICE NEW-ADS-SLICE-OPENER
                        SET::USE-WEAK-INSERT-INDUCTION
                        UNION-OF-2SET-AND-2SET
                        SET::WEAK-INSERT-INDUCTION)))))

(DEFTHM
  NEW-AD-OF-UNION-DOM-AND-N-NEW-ADSalt-better
  (IMPLIES
   (AND (NATP N) (<= 0 N))
   (EQUAL
    (NEW-AD (SET::UNION (LIST::|2SET| (N-new-ads2 N DOM)) DOM))
    (NTH-NEW-AD (+ 1 N) DOM)))
  :hints (("Goal" :in-theory (e/d (N-NEW-ADS-BECOMES-N-NEW-ADS2)( IN-OF-NEW-AD-AND-N-NEW-ADS IN-OF-NEW-AD-AND-N-NEW-ADS NEW-AD-NOT-MEMBERP-OF-NEW-ADS MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP NEW-AD-NOT-MEMBERP-OF-NEW-ADS-SLICE NEW-AD-OF-UNION-DOM-AND-N-NEW-ADSalt))
          :use (:instance NEW-AD-OF-UNION-DOM-AND-N-NEW-ADSalt)))
  :OTF-FLG T
)

(DEFTHM INSERT-OF-NEXT-AD-ONTO-UNION-OF-DOM-AND-N-NEW-ADSalt
  (IMPLIES
   (AND (EQUAL M (+ 1 N)) (NATP N) (< 0 N))
   (EQUAL
    (SET::INSERT (NTH-NEW-AD M DOM) (SET::UNION (LIST::|2SET| (N-NEW-ADS N DOM)) DOM))
    (SET::UNION DOM (LIST::|2SET| (N-NEW-ADS M DOM))))))

(in-theory (disable N-NEW-ADS2))
(in-theory (enable N-NEW-ADS-BECOMES-N-NEW-ADS2))

(DEFTHM INSERT-OF-NEXT-AD-ONTO-UNION-OF-DOM-AND-N-NEW-ADSalt-better
  (IMPLIES
   (AND (EQUAL M (+ 1 N)) (NATP N) (< 0 N))
   (EQUAL
    (SET::INSERT (NTH-NEW-AD M DOM) (SET::UNION (LIST::|2SET| (N-new-ads2 N DOM)) DOM))
    (SET::UNION DOM (LIST::|2SET| (N-new-ads2 M DOM)))))
  :hints (("Goal" :use (:instance INSERT-OF-NEXT-AD-ONTO-UNION-OF-DOM-AND-N-NEW-ADSalt)
           :in-theory (disable INSERT-OF-NEXT-AD-ONTO-UNION-OF-DOM-AND-N-NEW-ADSalt
                               INSERT-OF-NEXT-AD-ONTO-UNION-OF-DOM-AND-N-NEW-ADS))))

(DEFTHM INSERT-OF-NEXT-AD-ONTO-UNION-OF-DOM-AND-N-NEW-ADSalt-better-rev
  (IMPLIES
   (AND (EQUAL M (+ 1 N)) (NATP N) (< 0 N))
   (EQUAL
    (SET::INSERT (NTH-NEW-AD M DOM) (SET::UNION DOM (LIST::|2SET| (N-new-ads2 N DOM))))
    (SET::UNION DOM (LIST::|2SET| (N-new-ads2 M DOM)))))
  :hints (("Goal" :use (:instance INSERT-OF-NEXT-AD-ONTO-UNION-OF-DOM-AND-N-NEW-ADSalt)
           :in-theory (disable INSERT-OF-NEXT-AD-ONTO-UNION-OF-DOM-AND-N-NEW-ADSalt
                               INSERT-OF-NEXT-AD-ONTO-UNION-OF-DOM-AND-N-NEW-ADS))))



(defthm new-ad-not-equal-nth-new-ad2
  (implies (and (integerp n)
                (< 1 n))
           (equal (EQUAL (NEW-AD dom) (NTH-NEW-AD n dom))
                  nil)))

(defthm new-ad-not-equal-nth-new-ad2alt
  (implies (and (integerp n)
                (< 1 n))
           (equal (EQUAL (NTH-NEW-AD n dom) (NEW-AD dom))
                  nil)))

(DEFTHM NOT-MEMBERP-N-NEW-ADS2
  (IMPLIES (SET::IN AD DOM)
           (equal (MEMBERP AD (N-NEW-ADS N DOM))
                  nil))
  :hints (("Goal" :in-theory (disable N-NEW-ADS-BECOMES-N-NEW-ADS2))))

(DEFTHM NOT-MEMBERP-N-NEW-ADS2-better
  (IMPLIES (SET::IN AD DOM)
           (equal (MEMBERP AD (N-new-ads2 N DOM))
                  nil))
  :hints (("Goal" :use (:instance  NOT-MEMBERP-N-NEW-ADS2)
           :in-theory (e/d (n-new-ads-becomes-n-new-ads2) (  NOT-MEMBERP-N-NEW-ADS2 NOT-MEMBERP-N-NEW-ADS)))))


(defthm N-NEW-ADS2-AUX-of-0
  (equal (N-NEW-ADS2-AUX 0 CT DOM)
         nil)
  :hints (("Goal" :in-theory (enable N-NEW-ADS2-AUX))))

(defthm new-ad-aux-of-insert-of-next
  (implies (natp current-try)
           (equal (new-ad-aux (set::insert (new-ad-aux ads current-try) ads) current-try)
                  (new-ad-aux ads (+ 1 (new-ad-aux ads current-try)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable new-ad-aux NEW-AD-AUX-IS-CURRENT-TRY))))

(defthm n-new-ads2-aux-of-insert-new-ad-gen
  (implies (and; (<= current-try (new-ad ads))
                (natp n)
                (natp current-try))
           (equal (n-new-ads2-aux n current-try (set::insert (new-ad-aux ads current-try) ads))
                  (n-new-ads2-aux n (+ 1 (new-ad-aux ads current-try)) ads)))
  :hints (("Goal" :in-theory (enable n-new-ads2-aux)
           :do-not '(generalize eliminate-destructors))))

(defthm n-new-ads2-aux-of-insert-new-ad-gen-hack
  (implies (and; (<= current-try (new-ad ads))
            (equal ad (new-ad-aux ads current-try))
                (natp n)
                (natp current-try))
           (equal (n-new-ads2-aux n current-try (set::insert ad ads))
                  (n-new-ads2-aux n (+ 1 (new-ad-aux ads current-try)) ads)))
  :hints (("Goal" :in-theory (enable n-new-ads2-aux)
           :do-not '(generalize eliminate-destructors))))

(defthm new-ad-aux-of-union-irrel
   (implies (and (natp ct)
                 (not (set::in (new-ad-aux dom ct) s)))
            (equal (new-ad-aux (set::union dom s) ct)
                   (new-ad-aux dom ct)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :expand ((NEW-AD-AUX (SET::UNION DOM S) CT))
            :in-theory (enable NEW-AD-AUX NEW-AD-AUX-IS-CURRENT-TRY))))


(defthm N-NEW-ADS2-AUX-of-delete-irrel
  (implies (and (< ct ct2)
                (natp ct)
                (natp ct2))
           (equal (N-NEW-ADS2-AUX N CT2 (SET::DELETE CT DOM))
                  (N-NEW-ADS2-AUX N CT2 DOM)))
  :hints (("Goal" :in-theory (enable N-NEW-ADS2-AUX))))

(defthm memberp-of-n-new-ads2-aux-irrel
  (implies (and (< ct ct2)
                (natp ct)
                (natp ct2))
           (not (memberp ct (n-new-ads2-aux n ct2 dom))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable n-new-ads2-aux))))

(defthm memberp-of-new-ad-aux-and-n-new-ads2-aux-irrel
 (implies (and (< (new-ad-aux dom ct) ct2)
               (natp n)
               (natp ct)
               (natp ct2))
          (not (memberp (new-ad-aux dom ct)
                              (n-new-ads2-aux n ct2 dom))))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :expand ((new-ad-aux (set::union dom s) ct))
          :in-theory (enable new-ad-aux new-ad-aux-is-current-try))))

(defthm n-new-ads2-aux-of-sfix
  (equal (n-new-ads2-aux m ct (set::sfix dom))
         (n-new-ads2-aux m ct dom))
  :hints (("Goal" :in-theory (enable n-new-ads2-aux))))



;; (defthm nth-of-n-new-ads2-aux
;;   (implies (and (natp n)
;;                 (< m n)
;;                 (natp m)
;;                 (natp curr))
;;            (equal (nth m (n-new-ads2-aux n curr ads))
;;                   (nth-new-ad2 (+ m curr) ads)))
;;   :hints (("Goal" :in-theory (enable n-new-ads2-aux)
;;            :use (:instance recharacterize-nth-of-n-new-ads2-aux
;;                            (m (+ 1 m))))))

;; (thm
;;  (implies (and (natp n1)
;;                (natp n2)
;;                (< n1 n2)
;;                (natp curr))
;;           (equal (nthcdr n1 (n-new-ads2-aux n2 curr ads))
;;                  (n-new-ads2-aux (- n2 n1) (+ n1 curr) ads)))
;;  :hints (("Goal" :in-theory (enable n-new-ads2-aux))))

(defthm address-hack-bbbozo-better-helper
  (implies (and (natp m)
                (natp n)
                (natp ct)
;                (set::setp dom)
                )
           (equal (n-new-ads2-aux m ct (set::union dom (list::2set (n-new-ads2-aux n ct dom))))
                  (nthcdr n (n-new-ads2-aux (+ m n) ct dom))))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
            :induct (N-NEW-ADS2-AUX N CT DOM)
           :expand ( ;(n-new-ads2-aux (+ m n) 0 dom)

                    (N-NEW-ADS2-AUX N CT DOM)
                    (N-NEW-ADS2-AUX (+ M N) CT DOM)
                    (n-new-ads2-aux n 0 dom))
           :in-theory (e/d (new-ads-slice n-new-ads2
                                          ;N-NEW-ADS2-AUX
                                          (:induction n-new-ads2-aux)
                                          )
                           ( ;subrange-rewrite
                            SET::UNION
                            )))))

(defthm address-hack-bbbozo-better
   (implies (and (natp m)
                 (natp n))
            (equal (n-new-ads2 m (set::union dom (list::2set (n-new-ads2 n dom))))
                   (new-ads-slice (+ 1 n) (+ m n) dom)))
   :hints (("Goal" :in-theory (enable n-new-ads2 new-ads-slice))))


;; (skip-proofs
;; (defthm address-hack-bbbozo
;;    (implies (and (natp m)
;;                  (natp n)
;;                  (set::setp dom)
;;                  )
;;             (equal (n-new-ads m (set::union dom (list::2set (n-new-ads n dom))))
;;                    (new-ads-slice (+ 1 n) (+ m n) dom)))
;;    :hints (("Goal"
;;             :do-not '(generalize eliminate-destructors)
;; ;            :induct t
;;             :expand (n-new-ads-aux n dom)
;;             :in-theory (e/d (new-ads-slice n-new-ads (:induction n-new-ads-aux))
;;                             (subrange-rewrite N-NEW-ADS-BECOMES-N-NEW-ADS2))))))

(DEFTHM MEMBERP-OF-NTH-NEW-AD-AND-NEW-ADS-SLICE2
  (IMPLIES (AND (NATP N)
                (< 0 N)
                (NATP START)
                (NATP END)
                (<= START N)
                (<= N END))
           (equal (MEMBERP (NTH-NEW-AD N DOM)
                                 (NEW-ADS-SLICE START END DOM))
                  t)))

(DEFTHM NOT-MEMBERP-OF-NEW-ADS-SLICE2
  (IMPLIES (SET::IN AD DOM)
           (equal (MEMBERP AD (NEW-ADS-SLICE START END DOM))
                  nil))
  :hints (("Goal" :IN-THEORY (ENABLE NEW-ADS-SLICE))))

(defthm not-memberp-of-cdr-when-infirstn-and-unique
  (implies (and (natp n)
                (<= n (len lst))
                (memberp x (firstn n lst))
                (no-duplicatesp-equal lst))
           (equal (memberp x (nthcdr n lst))
                  nil))
  :hints (("Goal" :in-theory (e/d (nthcdr firstn no-duplicatesp-equal)
                                  (NTHCDR-OF-CDR-COMBINE-STRONG)))))

;; (defthm take-of-n-new-ads
;;   (implies (and (<= n m)
;;                 (natp n)
;;                 (natp m))
;;            (equal (take n (n-new-ads m ads))
;;                   (n-new-ads n ads)))
;;   :hints (("Goal" :in-theory (enable n-new-ads))))

;use lemma: not in nthcdr of x when in firstn x and x is unique..
;(skip -proofs
(defthm not-memberp-nth-new-ad-new-ads-slice
  (implies (and (or (< n start)
                    (< end n))
                (natp n)
                (< 0 n) ;new Sat Oct 22 00:08:46 2011 ;could drop because the 0th new ad (not really allowed) is the same as the 1st new ad
                (natp end)
;(posp start)
                (natp start))
           (equal (MEMBERP (NTH-NEW-AD N DOM) (NEW-ADS-SLICE START END DOM))
                  nil))
  :hints (("Goal"
           :use (:instance not-memberp-of-cdr-when-infirstn-and-unique (x (NTH-NEW-AD N DOM)) (n (+ -1 start)) (lst (N-NEW-ADS END DOM)))
           :in-theory (e/d (NEW-ADS-SLICE ;N-NEW-ADS
                            NTHCDR-WHEN-<-OF-LEN) (;;TAKE-OF-NTHCDR-BECOMES-SUBRANGE
                               CDR-OF-N-NEW-ADS
                               ;;NEW-ADS-SLICE
                            N-NEW-ADS-BECOMES-N-NEW-ADS2)))))
;)

;; (thm
;;  (equal (n-new-ads 11 (set::union dom (list::2set (n-new-ads 15 dom))))
;;         (new-ads-slice 16 26 dom))
;;  :hints (("Goal" :in-theory (enable new-ads-slice n-new-ads))))

;; (thm
;;  (IMPLIES
;;   (AND
;;    (NOT (ZP N))
;;    (EQUAL
;;     (REVERSE-LIST
;;      (N-NEW-ADS-AUX M
;;                     (SET::UNION DOM
;;                                 (LIST::|2SET| (N-NEW-ADS-AUX (+ -1 N) DOM)))))
;;     (NTHCDR (+ -1 N)
;;             (REVERSE-LIST (N-NEW-ADS-AUX (+ -1 M N) DOM))))
;;    (NATP M)
;;    (SET::SETP DOM))
;;   (EQUAL
;;    (REVERSE-LIST
;;     (N-NEW-ADS-AUX M
;;                    (SET::UNION DOM
;;                                (LIST::|2SET| (N-NEW-ADS-AUX N DOM)))))
;;    (NTHCDR N
;;            (REVERSE-LIST (N-NEW-ADS-AUX (+ M N) DOM)))))
;;  :hints (("Goal" :expand ((N-NEW-ADS-AUX N DOM)))))



(defthm new-ad-not-memberp-of-new-ads-slice2 ;new-ads-not-memberp-of-new-ads-slice
  (implies (and (< 1 start)
                (natp start))
           (equal (memberp (NEW-AD dom)
                                 (NEW-ADS-SLICE start end dom))
                  nil)))



(defthm union-commutative-2-2set-of-new-ads-slice
  (equal (set::union (list::|2SET| (new-ads-slice m n x))
                     (set::union x foo))
         (set::union x
                     (set::union (list::|2SET| (new-ads-slice m n x))
                                 foo))))


;; (thm
;;  (implies (and (< n (+ num-ads current-try))
;;                (< 0 num-ads)
;;                (natp n)
;;                ;; (<= current-try n)
;;                (natp num-ads)
;;                (< 0 n)
;;                ;; (not (memberp (nth-new-ad n dom) acc))
;;                (natp current-try))
;;           (equal (memberp (nth-new-ad n dom) (n-new-ads2-aux num-ads current-try dom acc))
;;                  t))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :in-theory (enable n-new-ads2-aux))))

(defthm not-memberp-of-firstn-when-memberp-of-nthcdr-and-unique
  (implies (and (natp n)
                (<= n (len lst))
                (memberp x (nthcdr n lst))
                (no-duplicatesp-equal lst))
           (equal (memberp x (firstn n lst))
                  nil))
  :hints (("Goal" :in-theory (e/d (nthcdr firstn no-duplicatesp-equal)
                                  (NTHCDR-OF-CDR-COMBINE-STRONG)))))


(defthm memberp-of-NEW-AD-AUX-and-N-NEW-ADS2-AUX
  (implies (posp n)
           (MEMBERP (NEW-AD-AUX DOM 0) (N-NEW-ADS2-AUX N 0 DOM)))
  :hints (("Goal" :in-theory (enable N-NEW-ADS2-AUX))))

(defthm unique-of-n-new-ads2-aux
  (implies (and (natp m)
                (natp ct))
           (no-duplicatesp-equal (n-new-ads2-aux m ct dom)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable n-new-ads2-aux ;no-duplicatesp-equal-of-cons
                              ))))

;; (local
;;  (defthm coi-memberp-becomes-memberp
;;    (equal (list::memberp a x)
;;           (memberp a x))
;;    :hints (("Goal" :in-theory (enable memberp list::memberp)))))

;move
(defthm memberp-when-memberp-of-firstn
  (implies (memberp a (firstn n x))
           (memberp a x)))

(defthm memberp-of-nth-new-ad-and-n-new-ads-better
  (implies (and (posp m)
                (natp n))
           (equal (memberp (nth-new-ad m dom) (n-new-ads2 n dom))
                  (<= m n)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use ((:instance not-memberp-of-firstn-when-memberp-of-nthcdr-and-unique
                            (lst (N-NEW-ADS2-AUX M 0 DOM))
                            (n n)
                            (x (NTH (+ -1 M) (N-NEW-ADS2-AUX M 0 DOM))))
                 (:instance memberp-when-memberp-of-firstn
                            (a (NTH (+ -1 M) (N-NEW-ADS2-AUX M 0 DOM)))
                            (n m)
                            (x (N-NEW-ADS2-AUX N 0 DOM)))
                 )
           :in-theory (e/d (n-new-ads2 RECHARACTERIZE-NTH-NEW-AD NTH-NEW-AD2 ;N-NEW-ADS2-AUX
                              ) (not-memberp-of-firstn-when-memberp-of-nthcdr-and-unique
                                 NOT-MEMBERP-OF-CDR-WHEN-INFIRSTN-AND-UNIQUE)))))

;; (skip-proofs
;; (defthm memberp-of-nth-new-ad-and-n-new-ads-better
;;    (implies (and (natp m)
;;                  (natp n))
;;             (equal (memberp (nth-new-ad m dom) (n-new-ads2 n dom))
;;                    (<= m n)))
;;    :hints (("Goal" :in-theory (enable n-new-ads2 RECHARACTERIZE-NTH-NEW-AD)))))

(defthm new-ad-union-2set-N-NEW-ADS-better
  (implies (natp n)
           (equal (NEW-AD (SET::UNION dom (LIST::|2SET| (N-NEW-ADS2 n dom))))
                  (NTH-NEW-AD (+ 1 N) DOM)))
  :hints (("Goal" :use (:instance NEW-AD-OF-UNION-DOM-AND-N-NEW-ADS)
           :in-theory (disable NEW-AD-OF-UNION-DOM-AND-N-NEW-ADS))))

(DEFTHM NTH-NEW-AD-OF-UNION-DOM-N-new-ads-better
  (IMPLIES (AND (NATP M) (< 0 M) (NATP N))
           (EQUAL
            (NTH-NEW-AD
             M
             (SET::UNION DOM (LIST::|2SET| (N-new-ads2 N DOM))))
            (NTH-NEW-AD (+ M N) DOM)))
  :hints (("Goal" :use (:instance NTH-NEW-AD-OF-UNION-DOM-N-NEW-ADS)
           :in-theory (disable NTH-NEW-AD-OF-UNION-DOM-N-NEW-ADS))))


(defthm take-of-N-NEW-ADS2
  (implies (and (<= m n)
                (natp m)
                (natp n))
           (equal (TAKE m (N-NEW-ADS2 n ADS))
                  (N-NEW-ADS2 m ADS)))
  :hints (("Goal" :in-theory (enable N-NEW-ADS2))))

;bozo why does the new-ads-slice not have 2set?
;bozo prove
;bozo more like this?
(defthm union-of-new-ads-slice-and-2set-of-n-new-ads-better
  (implies (and (equal low-1 (+ -1 low))
                (posp low)     ;(natp low)
                (<= low high)  ;new
                (natp high))
           (equal (set::union (list::2set (new-ads-slice low high dom)) (list::2set (n-new-ads2 low-1 dom)))
                  (list::2set (n-new-ads2 high dom))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (new-ads-slice UNION-OF-2SET-AND-2SET-BACK)
                                  ( ;LIST::EQUAL-APPEND-REDUCTION!-ALT LIST::APPEND-TAKE-NTHCDR LIST::EQUAL-APPEND-REDUCTION!
                                   UNION-OF-2SET-AND-2SET))
           :use (:instance APPEND-OF-TAKE-AND-NTHCDR-2 (l (N-NEW-ADS2 HIGH DOM))
                           (n (+ -1 low))))))

(defthm insert-of-new-ad-of-insert-of-nth-new-ad
  (equal (set::insert (new-ad x) (set::insert (nth-new-ad n x) s))
         (set::insert (nth-new-ad n x) (set::insert (new-ad x) s))))

(defthm insert-of-nth-new-ad-of-insert-of-nth-new-ad
  (implies (< m n)
           (equal (set::insert (nth-new-ad m x) (set::insert (nth-new-ad n x) s))
                  (set::insert (nth-new-ad n x) (set::insert (nth-new-ad m x) s)))))










;trying...
;; ;bozo handle this stuff better?
;; (skip -proofs
;;  (defthm nth-1-insert-new-ad-nth-new-ad-2
;;   (equal (NTH 1 (SET::INSERT (NEW-AD dom) (SET::INSERT (NTH-NEW-AD 2 dom) NIL)))
;;          (NTH-NEW-AD 2 dom))
;;   :hints (("Goal" :use (:instance LIST-NEW-AD-NTH-NEW-AD-2)
;;            :in-theory (disable LIST-NEW-AD-NTH-NEW-AD-2)))))

;; (skip -proofs
;;  (defthm nth-0-insert-new-ad-nth-new-ad-2
;;   (equal (NTH 0 (SET::INSERT (NEW-AD dom) (SET::INSERT (NTH-NEW-AD 2 dom) NIL)))
;;          (NEW-AD dom))
;;   :hints (("Goal" :use (:instance LIST-NEW-AD-NTH-NEW-AD-2)
;;            :in-theory (disable LIST-NEW-AD-NTH-NEW-AD-2)))))

(defthm memberp-of-nth-new-ad-and-N-NEW-ADS-aux
  (implies (and (posp n)
                (natp m)
                (<= n m))
           (MEMBERP (NTH-NEW-AD N dom)
                          (N-NEW-ADS-aux m dom)))
  :hints (("Goal" :in-theory (e/d (N-NEW-ADS-aux) (N-NEW-ADS-BECOMES-N-NEW-ADS2)))))

(defthm memberp-of-nth-new-ad-and-N-NEW-ADS
  (implies (and (posp n)
                (<= n m)
                (natp m))
           (MEMBERP (NTH-NEW-AD N dom)
                          (N-NEW-ADS m dom)))
  :hints (("Goal" :in-theory (e/d (N-NEW-ADS) (N-NEW-ADS-BECOMES-N-NEW-ADS2)))))

(defthm insert-of-nth-new-ad-when-already-there-lemma
  (implies (and (posp n)
                (natp m)
                (<= n m))
           (equal (SET::INSERT (NTH-NEW-AD n dom)
                               (SET::UNION (LIST::2SET (N-NEW-ADS m dom))
                                           dom))
                  (SET::UNION (LIST::2SET (N-NEW-ADS m dom))
                              dom)))
  :hints (("Goal" :in-theory (disable N-NEW-ADS-BECOMES-N-NEW-ADS2))))

;this just commutes the arguments to the union
(defthm insert-of-nth-new-ad-when-already-there-lemma-alt
  (implies (and (posp n)
                (natp m)
                (<= n m))
           (equal (SET::INSERT (NTH-NEW-AD n dom)
                               (SET::UNION dom
                                           (LIST::2SET (N-NEW-ADS m dom))))
                  (SET::UNION dom
                              (LIST::2SET (N-NEW-ADS m dom)))))
  :hints (("Goal" :in-theory (disable N-NEW-ADS-BECOMES-N-NEW-ADS2))))


(defthm insert-of-new-ad-when-already-there-lemma
  (implies (posp n)
           (equal (SET::INSERT (NEW-AD dom)
                               (SET::UNION (LIST::2SET (N-NEW-ADS n dom))
                                           dom))
                  (SET::UNION (LIST::2SET (N-NEW-ADS n dom))
                              dom))))


;this one has the union commuted differently:
(defthm insert-of-new-ad-when-already-there-lemma-alt
  (implies (posp n)
           (equal (SET::INSERT (NEW-AD dom)
                               (SET::UNION dom
                                           (LIST::2SET (N-NEW-ADS n dom))))
                  (SET::UNION dom
                              (LIST::2SET (N-NEW-ADS n dom))))))
