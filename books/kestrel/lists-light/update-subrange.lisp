; A utility to update part of a list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "update-nth"))
(local (include-book "append"))
(local (include-book "nthcdr"))
(local (include-book "len"))
(local (include-book "take"))
(local (include-book "cons"))
(local (include-book "true-list-fix"))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

;move
;BOZO might cause case splits?
(defthm nthcdr-update-nth-better
  (equal (nthcdr n (update-nth n2 v l))
         (if (< (nfix n2) (ifix n))
             (nthcdr n l)
           (update-nth (- (nfix n2) (nfix n))
                       v (nthcdr n l))))
  :hints (("Goal" :in-theory (enable nthcdr update-nth))))

;dup?
(defund update-subrange (start end vals lst)
  (declare (xargs :measure (nfix (+ 1 (- end start)))
                  :guard (and (rationalp start)(rationalp end) (true-listp vals) (true-listp lst))
                  :verify-guards nil ;done below
                  ))
  (if (or (< end start)
          (not (natp start))
          (not (natp end)))
      lst
      (update-nth start (nth 0 vals)
                  (update-subrange (+ 1 start)
                                   end (cdr vals)
                                   lst))))

(defthm update-nth-of-update-subrange-diff
  (implies (and (natp n)
                (natp start)
                (natp end)
                (< n start))
           (equal (update-nth n val (update-subrange start end vals lst))
                  (update-subrange start end vals (update-nth n val lst))))
  :hints (("Goal" :in-theory (enable update-subrange update-nth-of-update-nth-diff))))

(defthmd update-nth-of-update-subrange-diff-back
  (implies (and (natp n)
                (natp start)
                (natp end)
                (< n start))
           (equal (update-subrange start end vals (update-nth n val lst))
                  (update-nth n val (update-subrange start end vals lst))
                  ))
  :hints (("Goal" :in-theory (enable update-nth-of-update-nth-diff))))

(defthm true-listp-of-update-subrange
  (implies (true-listp lst)
           (true-listp (update-subrange start end vals lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (update-subrange UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF-BACK)
                           (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

(verify-guards update-subrange)

(defthm nth-of-update-subrange-same
  (implies (and (natp start)
                (integerp end) ;(natp end)
                (natp n)
                (<= start n)
                (<= n end))
           (equal (NTH n (UPDATE-SUBRANGE start end vals lst))
                  (nth (- n start) vals)))
  :hints (("subgoal *1/4" :expand  (UPDATE-SUBRANGE N END VALS LST))
          ("Goal" :in-theory (e/d ( update-subrange ;nth
                                   ) (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

(defthm nth-of-update-subrange-diff-1
  (implies (and (natp start)
                (integerp end) ;(natp end)
                (natp n)
                (> start n)
                )
           (equal (nth n (update-subrange start end vals lst))
                  (nth n lst)))
  :hints (("Goal" :in-theory (e/d (update-subrange) (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

(defthm nth-of-update-subrange-diff-2
  (implies (and (natp start)
                (integerp end) ;(natp end)
                (natp n)
                (< end n)
                )
           (equal (nth n (update-subrange start end vals lst))
                  (nth n lst)))
  :hints (("Goal" :in-theory (e/d (update-subrange) (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

;disable the individual cases?
(defthm nth-of-update-subrange
  (implies (and (natp start)
                (natp end)
                (natp n))
           (equal (nth n (update-subrange start end vals lst))
                  (if (or (< n start)
                          (< end n))
                      (nth n lst)
                    (nth (+ n (- start)) vals)))))

(local
 (defthm arith-helper
   (implies (acl2-numberp start1)
            (equal (EQUAL -1 (+ END1 (- START1)))
                   (EQUAL start1 (+ 1 END1))))))

(defthm update-subrange-combine-adjacent-1
  (implies (and (natp end1)
                (natp start1)
                ;; (natp start2)
                (natp end2)
                (<= start2 end2)
                (equal (len vals1) (+ 1 end1 (- start1)))
                (equal start2 (+ 1 end1)))
           (equal (update-subrange start1 end1 vals1 (update-subrange start2 end2 vals2 lst))
                  (update-subrange start1 end2 (append vals1 vals2) lst)))
  :hints (("Goal" :in-theory (e/d (update-subrange)
                                  ( ;LEN-OF-CDR ;why? changes the induction scheme?
                                      )))))

(defthm take-of-update-subrange-irrel
  (implies (and (<= n start)
                (natp n)
                (natp start))
           (equal (take n (update-subrange start end vals lst))
                  (take n lst)))
  :hints (("Goal" :in-theory (e/d (update-subrange update-nth-of-update-subrange-diff-back)
                                  (update-nth-of-update-subrange-diff)))))

(defthm update-subrange-start-start
  (implies (and (natp start))
           (equal (update-subrange start start vals lst)
                  (update-nth start (car vals) lst)))
  :hints (("Goal" :in-theory (enable nth update-subrange)
           :expand ((update-subrange start start vals lst)))))

;disable?
(defthm update-nth-of-update-nth-becomes-update-subrange
  (implies (and (equal n2 (+ 1 n1))
                (natp n1))
           (equal (update-nth n1 val1 (update-nth n2 val2 lst))
                  (update-subrange n1 n2 (list val1 val2) lst)))
  :hints (("Goal" :in-theory (enable update-subrange))))

;;i've seen this loop
(defthmd update-subrange-split-off-last-elem
  (implies (and (natp end)
                (natp start)
                (equal (len vals) (+ 1 end (- start)))
                )
           (equal (update-subrange start (+ 1 end) (append vals (list val)) lst)
                  (update-nth (+ 1 end) val (update-subrange start end vals lst))))
  :hints ( ;("Subgoal *1/4" :cases ((equal end start)))
          ("Goal" :expand ((UPDATE-SUBRANGE (+ 2 END)
                                            (+ 1 END)
                                            NIL LST))
           :in-theory (e/d (update-subrange)
                           (    ;LIST::LEN-WHEN-AT-MOST-1        ;for speed
                            len ;for speed
                            UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

(defthm update-nth-of-update-subrange
  (implies (and (natp end)
                (natp start)
                (equal (len vals) (+ 1 end (- start)))
                (equal n (+ 1 end)))
           (equal (update-nth n val (update-subrange start end vals lst))
                  (update-subrange start (+ 1 end) (append vals (list val)) lst)))
  :hints (("Goal" :in-theory (enable update-subrange-split-off-last-elem))))

(defthm update-subrange-of-update-subrange-same
  (implies (and (natp start)
                (natp end))
           (equal (update-subrange start end vals1 (update-subrange start end vals2 lst))
                  (update-subrange start end vals1 lst)))
  :hints (("Goal" :expand (     (UPDATE-SUBRANGE START END VALS1
                                                 (UPDATE-SUBRANGE (+ 1 START)
                                                                  END (CDR VALS2)
                                                                  (UPDATE-NTH START (NTH 0 VALS2) LST)))

                                (update-subrange start end val1
                                                 (update-subrange (+ 1 start)
                                                                  end (cdr vals2)
                                                                  (update-nth start (nth 0 vals2) lst))))
           :in-theory (e/d (update-subrange update-nth-of-update-subrange-diff-back) ( update-nth-of-update-subrange-diff))
           :do-not '(generalize eliminate-destructors))))

(defthm update-subrange-of-take
  (equal (update-subrange start end (take (+ 1 end (- start)) vals) lst)
         (update-subrange start end vals lst))
  :hints (("Goal" :in-theory (e/d (update-subrange; take-rewrite
                                   ;CDR-TAKE-PLUS-1
                                   ) (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

(defthm update-subrange-reorder
  (implies (and (<= start1 end1)
                (<= start2 end2)
                (< end2 start1)
                (natp start1)
                (natp end1)
                (natp start2)
                (natp end2)
                )
           (equal (update-subrange start1 end1 vals1 (update-subrange start2 end2 vals2 lst))
                  (update-subrange start2 end2 vals2 (update-subrange start1 end1 vals1 lst))))
  :hints (("Goal" :in-theory (enable update-subrange))))

;rename
(defthm take-of-update-subrange
  (implies (<= n (nfix start))
           (equal (take n (update-subrange start end vals lst))
                  (take n lst)))
  :hints (("Goal" :use (:instance take-of-update-subrange-irrel (start (nfix start)))
           :in-theory (e/d (take)
                           (take-of-update-subrange-irrel)))))

(defthm nthcdr-of-update-subrange
  (implies (and ; (<= n start)
            (< end n) ;drop and handle other cases?
            (natp n)
            (natp start)
;            (equal (+ 1 end (- start)) (len vals))
            )
           (equal (nthcdr n (update-subrange start end vals lst))
                  (nthcdr n lst)))
  :hints (("Goal" :in-theory ( e/d (update-subrange update-nth-of-update-subrange-diff-back)
                                   (update-nth-of-update-subrange-diff
                                    ;;take-of-nthcdr-becomes-subrange
                                    )))))

(defthm UPDATE-SUBRANGE-out-of-order
  (implies (> START END)
           (equal (UPDATE-SUBRANGE START END VALS LST)
                  lst))
  :hints (("Goal" :in-theory (enable UPDATE-SUBRANGE))))

(defthm nthcdr-of-update-subrange-less
  (implies (and (<= n start)
                (natp start)
                (natp end)
                (natp n)
;                (<= start end)
;                (equal (+ 1 end (- start)) (len vals))
                )
           (equal (nthcdr n (update-subrange start end vals lst))
                  (update-subrange (- start n) (- end n) vals (nthcdr n lst))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (update-subrange update-nth-of-update-subrange-diff-back) (update-nth-of-update-subrange-diff)))))

(defthm len-of-update-subrange
  (equal (len (update-subrange start end vals lst))
         (if (and (<= start end) (natp end) (natp start))
             (max (len lst) (+ 1 end))
           (len lst)))
  :hints (("Goal" :in-theory (e/d (update-subrange LEN-UPDATE-NTH update-nth-of-update-subrange-diff-back)
                                  (update-nth-of-update-subrange-diff)))))

(defthm consp-of-update-subrange
  (implies (and; (< end (len lst))
                (natp end)
                (natp start))
           (equal (consp (UPDATE-SUBRANGE start END vals LST))
                  (or (<= start end)
                      (consp lst))))
  :hints (("Goal" :in-theory (e/d (update-subrange update-nth-of-update-subrange-diff-back) (update-nth-of-update-subrange-diff)))))

;rename
(defthm car-of-update-subrange
  (implies (posp start)
           (equal (car (UPDATE-SUBRANGE START END VALS LST))
                  (car lst)))
  :hints (("Goal" :in-theory (e/d (update-subrange UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF-BACK) (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

(defthm car-of-update-subrange-of-0
  (equal (car (UPDATE-SUBRANGE 0 END VALS LST))
         (if (natp end)
             (car vals)
           (car lst)))
  :hints (("Goal" :expand (UPDATE-SUBRANGE 0 END VALS LST)
           :in-theory (enable update-subrange))))

(defthm cdr-of-update-subrange-from-non-zero
  (implies (and (natp end)
                (< 0 start)
                (natp start))
           (equal (cdr (update-subrange start end vals lst))
                  (update-subrange (+ -1 start) (+ -1 end) vals (CDR lst))))
  :hints (("Goal" :expand (update-subrange 0 end vals lst)
           :in-theory (e/d (update-subrange UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF-BACK)
                           (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

(defthm cdr-of-update-subrange-from-zero
  (implies (and (natp end))
           (equal (cdr (update-subrange 0 end vals lst))
                  (update-subrange 0 (+ -1 end) (cdr vals) (CDR lst))))
  :hints (("Goal" :expand (update-subrange 0 end vals lst)
           :in-theory (e/d (update-subrange UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF-BACK)
                           (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

(DEFTHM NTHCDR-OF-UPDATE-SUBRANGE-LESS-better
  (IMPLIES (AND (<= N START)
                (EQUAL (+ 1 END (- START)) (LEN VALS))
                (NATP START)
                (NATP END)
                (NATP N)
                )
           (EQUAL (NTHCDR N (UPDATE-SUBRANGE START END VALS LST))
                  (if (<= START END)
                      (UPDATE-SUBRANGE (- START N)
                                       (- END N)
                                       VALS (NTHCDR N LST))
                    (NTHCDR N LST)))))

;; (thm
;;  (implies (and (natp n)
;;                (natp n2))
;;           (equal (update-nth n (take n2 x))
;;                  (<

(defthm equal-of-update-nth-of-0
  (equal (equal (update-nth 0 val lst) x)
         (and (consp x)
              (equal (car x) val)
              (equal (cdr x) (cdr lst))))
  :hints (("Goal" :in-theory (enable update-nth))))

(local
 (defun ind (n end vals lst)
  (if  (zp n)
      (list n end vals lst)
    (ind (+ -1 n) (+ -1 end) (cdr vals) (cdr lst)))))

(defthm take-of-update-subrange-of-0-low
  (implies (and (<= n (+ 1 end))
                (natp end)
                (natp n))
           (equal (take n (update-subrange 0 end vals lst))
                  (take n vals)))
  :hints (("Goal" :induct (ind n end vals lst) ;:induct (take end (update-subrange 0 end vals lst))
           :in-theory (e/d (take update-subrange)
                           (equal-of-cons)))))

(defthm update-subrange-of-0
  (equal (update-subrange 0 end vals lst)
         (if (natp end)
             (append (take (+ 1 end) vals)
                     (nthcdr (+ 1 end) lst))
           lst))
  :hints (("Goal" :in-theory (enable equal-of-append
                                     update-subrange))))

(local
 (defun ind2 (n start end vals lst)
  (if  (zp n)
      (list n start end vals lst)
    (ind2 (+ -1 n) (+ -1 start) (+ -1 end) (cdr vals) (cdr lst)))))

(defthm nthcdr-of-update-subrange-half
  (implies (and (equal (+ 1 end (- start)) (len vals))
                (> n start)
                (<= n end)
                (natp n)
                ;; (integerp end) ;why needed for ACL2 6.2?
;                (<= start end)
                (natp start)
                )
           (equal (nthcdr n (update-subrange start end vals lst))
                  (update-subrange 0 (+ end (- n)) (nthcdr (+ n (- start)) vals) (nthcdr n lst))))
  :hints
  (("Goal"
    :do-not '(generalize eliminate-destructors)
    :in-theory
    (e/d (update-subrange
          ;;subrange
          update-nth-of-update-subrange-diff-back natp
          ;;NTHCDR
          )
         (update-nth-of-update-subrange-diff
          ;;anti-subrange
          )))))

;replace the other one
(DEFTHM NTHCDR-OF-UPDATE-SUBRANGE-LESS-BETTER-better
  (IMPLIES (AND (<= N START)
    ;                            (EQUAL (+ 1 END (- START)) (LEN VALS))
                (NATP START)
                (NATP END)
                (NATP N))
           (EQUAL (NTHCDR N (UPDATE-SUBRANGE START END VALS LST))
                  (IF (<= START END)
                      (UPDATE-SUBRANGE (- START N)
                                       (- END N)
                                       VALS (NTHCDR N LST))
                      (NTHCDR N LST))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (UPDATE-SUBRANGE UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF-BACK) (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

(DEFTHM NTHCDR-OF-UPDATE-SUBRANGE-better
  (IMPLIES (AND (> N END)
                (NATP N)
                (NATP START)
;                (EQUAL (+ 1 END (- START)) (LEN VALS))
                )
           (EQUAL (NTHCDR N (UPDATE-SUBRANGE START END VALS LST))
                  (NTHCDR N LST)))
  :HINTS (("Goal"
           :IN-THEORY
           (E/D ( UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF-BACK UPDATE-SUBRANGE)
                (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

(in-theory (disable NTHCDR-OF-UPDATE-SUBRANGE))

;; (defthm nthcdr-of-update-subrange-middle
;;   (implies (and (<= start n)
;;                 (<= n (+ 1 end)) ;gen?
;;                 (natp start)
;;                 (natp end)
;;                 (natp n)
;;                 (<= start end) ;gen
;;                 )
;;            (equal (nthcdr n (update-subrange start end vals lst))
;;                   (update-subrange (- start n)
;;                                    (- end n)
;;                                    (nthcdr (- n start) vals)
;;                                    (nthcdr n lst))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :induct (ind2 n start end vals lst)
;; ;           :expand (NTHCDR N (UPDATE-SUBRANGE START END VALS LST))
;;            :in-theory (e/d (;update-subrange
;;                             update-nth-of-update-subrange-diff-back) (update-nth-of-update-subrange-diff)))))

(defthm take-of-update-subrange-lemma
  (implies (and (<= n (+ 1 end))
;                (< end (len lst))
;                (equal (+ 1 end (- start)) (len vals))
                (natp start)
                (natp end)
                (natp n)
                (<= start n) ;gen
                )
           (equal (take n (update-subrange start end vals lst))
                  (append (take start lst)
                          (take (- n start) vals))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (UPDATE-SUBRANGE START END VALS LST)
           :in-theory (e/d (equal-of-append
                            ;equal-of-cons
                            ;;nth-when-n-is-zp
                            ;LIST::EQUAL-CONS-CASES ;JVM::CONS-EQUAL-REWRITE
                            ;LIST::LEN-UPDATE-NTH-BETTER
                            take
                            ;cons-car-self-equal-self
                            (:i update-subrange)
                            update-nth-of-update-subrange-diff-back)
                           ((:d update-subrange)
                            ;;NTHCDR-OF-UPDATE-SUBRANGE-LESS
                            ;TAKE-OF-CDR-BECOMES-SUBRANGE
                            update-nth-of-update-subrange-diff)))))
;bozo could just define it this way
(defthmd update-subrange-rewrite
  (implies (and ; (equal (+ 1 end (- start)) (len vals))
;                (< end (len lst))
;(true-listp lst) ;bozo
            (<= start end) ;new
            (natp start)
            (natp end)
;(true-listp vals)
            )
           (equal (update-subrange start end vals lst)
                  (if (<= start end)
                      (append (take start lst)
                              (take (+ 1 end (- start)) vals)
                              (nthcdr (+ 1 end) lst))
                    lst)))
  :hints (("Goal" ;:induct (indf n lst v)
           :cases ((< end (len lst)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable equal-of-append))))

(defthmd update-subrange-rewrite-better
  (implies (and (natp start)
                (natp end)
                )
           (equal (update-subrange start end vals lst)
                  (if (<= start end)
                      (append (take start lst)
                              (take (+ 1 end (- start)) vals)
                              (nthcdr (+ 1 end) lst))
                    lst)))

  :hints (("Goal" :use (:instance update-subrange-rewrite)
           :in-theory (disable update-subrange-rewrite ;LIST::EQUAL-APPEND-REDUCTION!
                               ))))

;similar to above
(defthm update-subrange-from-0
  (implies (and (equal (+ 1 n) (len vals))
                (natp n)
                (< n (len lst))
                )
           (equal (update-subrange 0 n vals lst)
                  (append vals (nthcdr (+ 1 n) lst)))))

(defthm update-subrange-not-nil1
  (implies (consp lst)
           (equal (equal (update-subrange start end vals lst) nil)
                  nil)))

(defthm update-subrange-not-nil2
  (implies (consp lst)
           (equal (equal nil (update-subrange start end vals lst))
                  nil)))

(defthm update-subrange-of-true-list-fix
  (equal (update-subrange start end (true-list-fix vals) lst)
         (update-subrange start end vals lst))
  :hints (("Goal" :in-theory (enable update-subrange true-list-fix))))

;move
;or phrase using finalcdr
(defthm nthcdr-when-<=-of-len
  (implies (and (<= (len x) (nfix n))
                (true-listp x))
           (equal (nthcdr n x) nil))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm update-subrange-all
  (implies (and (true-listp lst) ;bozo
                (true-listp v)
                (equal n (+ -1 (len lst)))
;(natp n)
;(equal (+ 1 n) (len lst))
;(equal (+ 1 n) (len v))
                (equal (len lst) (len v)))
           (equal (UPDATE-SUBRANGE 0 n v lst)
                  v))
  :hints (("Goal" ; :induct (indf n lst v)
           :in-theory (enable equal-of-append update-subrange-rewrite ;update-subrange
                              ))))

;; (defun indf (n lst1 lst2)
;;   (if (endp lst1)
;;       (list n lst1 lst2)
;;     (indf (+ -1 n) (cdr lst1) (cdr lst2))))



;; (defthm update-subrange-all-better
;;   (implies (and (true-listp lst) ;bozo
;; ;                (true-listp v)
;;                 (equal n (+ -1 (len lst)))
;; ;(natp n)
;; ;(equal (+ 1 n) (len lst))
;; ;(equal (+ 1 n) (len v))
;;                 (equal (len lst) (len v)))
;;            (equal (UPDATE-SUBRANGE 0 n v lst)
;;                   (true-list-fix v)))
;;   :hints (("Goal" ; :induct (indf n lst v)
;;            :in-theory (enable update-subrange-rewrite ;update-subrange
;;                               ))))
