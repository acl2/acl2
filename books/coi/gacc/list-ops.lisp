#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "GACC")

(include-book "mem")
(include-book "memberp" :dir :lists)
(include-book "basic" :dir :bags)

(include-book "list-ops-common")

;try to include less of super-ihs:
(include-book "super-ihs" :dir :super-ihs)

;; Operations for reading and writing lists of bytes.  Perhaps all fancier
;; reads and writes should be phrased in terms of rd-list and wr-list?  If so,
;; the interesting parts of those fancier operations would be how they
;; generate the lists of bytes and indices to be operated on by rd-list and
;; wr-list.

;;
;; RD-LIST
;;

;; Read the bytes from RAM that reside at the addresses in LIST.  Return a
;; list of the bytes in the same order as the addresses.  bzo disable this?
;;

(defund rd-list (list ram)
  (declare (type t list ram))
  (if (consp list)
      (cons (rd (car list) ram)
            (rd-list (cdr list) ram))
    nil))

(defthm rd-list-append
  (equal (rd-list (append x y) ram)
         (append (rd-list x ram)
                 (rd-list y ram)))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm len-rd-list
  (equal (len (rd-list list ram))
         (len list))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm car-of-rd-list
  (equal (car (rd-list lst ram))
         (if (consp lst)
             (rd (car lst) ram)
           nil))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm consp-of-rd-list
  (equal (consp (rd-list lst ram))
         (consp lst))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm cdr-of-rd-list
  (equal (cdr (rd-list list ram))
         (if (endp list)
             nil
           (rd-list (cdr list) ram)))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm integer-listp-of-rd-list
  (integer-listp (rd-list list ram))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm rd-list-of-singleton
  (equal (rd-list (list ad) ram)
         (list (rd ad ram)))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm rd-list-of-cons
  (equal (rd-list (cons ad ads) ram)
         (cons (rd ad ram) (rd-list ads ram)))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm rd-list-when-ads-is-not-a-consp
  (implies (not (consp ads))
           (equal (rd-list ads ram)
                  nil))
  :hints (("Goal" :in-theory (enable rd-list))))

(defthm nthcdr-of-rd-list
  (equal (nthcdr n (rd-list ads ram))
         (rd-list (nthcdr n ads) ram))
  :hints (("Goal" :in-theory (enable nthcdr rd-list))))                 

(defthm nth-of-rd-list
  (equal (nth n (rd-list ads ram))
         (if (< (nfix n) (len ads))
             (rd (nth n ads) ram)
           nil))
  :hints (("Goal" :in-theory (enable nth))))

(defthm firstn-of-rd-list
  (equal (firstn n (rd-list ads ram))
         (rd-list (firstn n ads) ram))
  :hints (("Goal" :in-theory (enable rd-list (:induction firstn)))))

;;
;; WR-LIST
;;
;;
;; Write to RAM each value from VALS at the corresponding address from LIST.
;; Stop when you run out of addresses.
;;
;; Note that once VALS runs out we use nil as the value for each subsequent
;; write.  You may think we should write 0's instead, but wr treats nil as a 0
;; when writing it.
;;
;;I changed this to not stop when vals runs out.  A key property of wr-list is
;;that we should be able to tell what addresses get changes just by looking at
;;LIST -- not by looking at VALS.  (Consider the case in which we call wr with
;;some address ad and then call wr-list with a list of addresses that contains
;;ad.  We should be able to prove that the call to wr can be dropped, and we
;;don't want to consider the case when the call to wr-list ends early because
;;it runs out of values. I proved that the new and old behvior is identical in
;;the one place in the regression suite that wr-list is called by another
;;defun. -ews
;;
;bzo rename list param to ads?
;bzo disable 

;bzo give a fast body?
(defund wr-list (list vals ram)
  (declare (type t list ram)
           (type (satisfies true-listp) vals))
  (if (and (consp list)
           ;(consp vals)
           )
      (wr (car list) (car vals) 
          (wr-list (cdr list) (cdr vals) ram))
    ram))

(defthmd open-wr-list
  (implies
   (consp list)
   (equal (wr-list list vals ram)
          (wr (car list) (car vals) 
              (wr-list (cdr list) (cdr vals) ram))))
  :hints (("goal" :in-theory (enable wr-list))))

(defthm wr-list-of-cons-one
  (equal (wr-list (cons ad ads) vals ram)
         (wr ad (car vals)  (wr-list ads (cdr vals) ram)))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm wr-list-of-cons-two
  (equal (wr-list ads (cons v vals) ram)
         (if (consp ads)
             (wr (car ads) v (wr-list (cdr ads) vals ram))
           ram))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm wr-list-of-cons-and-cons
  (equal (wr-list (cons ad list) (cons val vals) ram)
         (wr ad val (wr-list list vals ram))))

(defthm wr-list-when-ads-is-not-a-consp
  (implies (not (consp ads))
           (equal (wr-list ads vals ram)
                  ram))
  :hints (("Goal" :in-theory (enable wr-list))))
                 
(defthm wr-list-over-wr
  (implies (not (memberp x list))
           (equal (wr-list list vals (wr x v ram))
                  (wr x v (wr-list list vals ram))))
  :hints (("Goal" :in-theory (enable list::memberp-of-cons wr-list))))

(defthm wr-list-append
  (implies (and (disjoint x y)
                (equal (len x)
                       (len a)))
           (equal (wr-list (append x y) (append a b) ram)
                  (wr-list y b (wr-list x a ram))))
  :hints (("goal" :induct (list::len-len-induction x a)
           :in-theory (enable disjoint binary-append)))) 

(defthm rd-list-of-wr-irrel
  (implies (not (list::memberp ad ads))
           (equal (rd-list ads (wr ad v ram))
                  (rd-list ads ram)))
  :hints (("Goal" :in-theory (enable rd-list))))
 
(defthm wfixlist-rd-list
  (equal (wfixlist (rd-list list ram))
         (rd-list list ram))
  :hints (("Goal" :in-theory (enable wfixlist rd-list))))

;; (thm
;;  (equal (wr-list ads v1 (wr-list ads v2 ram))
;;         (wr-list ads v1 ram))
;;  :hints (("Goal" :in-theory (enable wr==r!))))
        
;bzo move
(defthm wr-list-of-wr-same
  (implies (memberp x list)
           (equal (wr-list list vals (wr x v ram))
                  (wr-list list vals ram)))
  :hints (("Goal" :in-theory (enable wr-list))))





;bzo move
(defthm wr-list-of-wr-list-subbagp
  (implies (bag::subbagp ads2 ads1)
           (equal (wr-list ads1 vals1 (wr-list ads2 vals2 ram))
                  (wr-list ads1 vals1 ram)))
  :Hints (("Goal" :induct (wr-list ads2 vals2 ram)
           :in-theory (enable wr-list)
           )))

(defthm wr-list-of-what-was-already-there
  (implies (equal vals (rd-list ads ram))
           (equal (wr-list ads vals ram)
                  ram))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm wr-list-of-what-was-already-there-cheap
  (equal (wr-list ads (rd-list ads ram) ram)
         ram))

(defthm wfixedlist-of-rd-list
  (wfixedlist (rd-list ads ram))
  :hints (("Goal" :in-theory (enable wfixedlist rd-list)))
  )


(defthm wr-list-of-wr-list-diff
  (implies (bag::disjoint list1 list2)
           (equal (wr-list list1 vals1 (wr-list list2 vals2 ram))
                  (wr-list list2 vals2 (wr-list list1 vals1 ram))))
  :hints (("Goal" :in-theory (enable wr-list))))

(defthm rd-of-wr-list-diff
  (implies (not (memberp ad ads))
           (equal (rd ad (wr-list ads val ram))
                  (rd ad ram)))
  :hints (("Goal" :in-theory (enable wr-list))))
                 
(defthm rd-list-of-wr-list-diff
  (implies (bag::disjoint ads1 ads2)
           (equal (rd-list ads1 (wr-list ads2 vals ram))
                  (rd-list ads1 ram)))
  :hints (("Goal" :in-theory (enable wr-list))))


;; (defun clr-list (ads ram)
;;   (if (endp ads)
;;       ram
;;     (clr-list (cdr ads) (clr (car ads) ram))))

(defun clr-list (ads ram)
  (if (consp ads)
      (clr-list (cdr ads) (memory-clr (car ads) ram))
    ram))

(defthmd open-clr-list
  (implies
   (consp ads)
   (equal (clr-list ads ram)
          (clr-list (cdr ads) (memory-clr (car ads) ram)))))

(defthmd clr-list-over-memory-clr
  (equal (clr-list list (memory-clr x r))
         (memory-clr x (clr-list list r)))
  :hints (("Subgoal *1/1" :cases ((equal x (car list))))))

#+joe
(defund clr-list (ads ram)
  (wr-list ads nil ram))

(defthm clr-list-when-ads-is-not-a-consp
  (implies (not (consp ads))
           (equal (clr-list ads ram)
                  ram))
  :hints (("Goal" :in-theory (enable clr-list))))



(defthm clr-list-of-wr-list-same
  (equal (clr-list ads (wr-list ads vals ram1))
         (clr-list ads ram1))
  :hints (("Goal" :in-theory (enable clr-list-over-memory-clr wr-list open-wr-list open-clr-list))))

(defthm clr-list-of-cons
  (equal (clr-list (cons ad ads) ram)
         (memory-clr ad (clr-list ads ram)))
  :hints (("Goal" :in-theory (enable clr-list-over-memory-clr  clr-list))))

(defthm clr-list-of-wr-cover
  (implies (list::memberp ad ads)
           (equal (clr-list ads (wr ad val ram))
                  (clr-list ads ram)))
  :hints (("Goal" :in-theory (enable clr-list))))

(local (defun my-induct (ads vals ram)
         (if (endp ads)
             (list ads vals ram)
           (my-induct (cdr ads) (cdr vals) (wr (car ads) (car vals) ram)))))

;; The unique hyp is necessary (unless we are willing to make the RHS more
;; complicated).  Consider: (rd-list '(0 0 0) (wr-list '(0 0 0) '(1 2 3) nil))
;; = (1 1 1)
;;
(defthm rd-list-of-wr-list-same
  (implies (bag::unique ads)
           (equal (rd-list ads (wr-list ads vals ram))
                  (my-wfixlist (len ads) vals)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable rd-list wr-list my-wfixlist)
           :induct (my-induct ads vals ram))))


;version for rd-list?
(defthm rd-subst-when-wr-list-equal
  (implies (and (equal (wr-list ads v ram1)
                       (wr-list ads v ram2))
                (syntaxp (acl2::smaller-term ram2 ram1))
                (not (memberp ad ads)))
           (equal (rd ad ram1)
                  (rd ad ram2)))
  :hints (("Goal" :use ((:instance rd-of-wr-list-diff (val v) (ram ram1))
                        (:instance rd-of-wr-list-diff (val v) (ram ram2))))))

(defthm wr-list-subst-wr-list
  (implies (and (equal (wr-list ads1 v1 ram1)
                       (wr-list ads1 v1 ram2))
                (syntaxp (acl2::smaller-term ram1 ram2))
                (subbagp ads1 ads2))
           (equal (wr-list ads2 v2 ram2)
                  (wr-list ads2 v2 ram1)))
  :hints (("Goal" :use ((:instance wr-list-of-wr-list-subbagp (ads1 ads2) (ads2 ads1) (vals1 v2) (vals2 v1) (ram ram2))
                        (:instance wr-list-of-wr-list-subbagp (ads1 ads2) (ads2 ads1) (vals1 v2) (vals2 v1) (ram ram1)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (disable wr-list-of-wr-list-subbagp))))

;It's a bit odd to replace vals with NIL, since NIL has a shorter length, but
;we do it anyway...
;
(defthm wr-list-equal-rewrite-vals-to-nil
  (implies (syntaxp (not (equal vals ''nil)))
           (equal (equal (wr-list ads vals ram2) (wr-list ads vals ram1))
                  (equal (wr-list ads nil ram2) (wr-list ads nil ram1)))))
        

;gen the len of ads?
(defthm wr-list-of-my-wfixlist
  (equal (wr-list ads (my-wfixlist (len ads) vals) ram)
         (wr-list ads vals ram))
  :hints (("Goal" :in-theory (enable wr-list my-wfixlist))))

(defthm wr-list-subst-vals
  (implies (and (equal (my-wfixlist (len ads) vals1)
                       (my-wfixlist (len ads) vals2))
                (syntaxp (acl2::smaller-term vals2 vals1)))
           (equal (wr-list ads vals1 ram)
                  (wr-list ads vals2 ram)))
  :hints (("Goal" :use ((:instance wr-list-of-my-wfixlist (vals vals1))
                        (:instance wr-list-of-my-wfixlist (vals vals2)))
           :in-theory (disable wr-list-of-my-wfixlist) ))) 


;; The (unique ads) hyp is necessary.  If ads contains duplicates but the
;; corresponding values in vals don't agree, then (my-wfixlist (len ads) vals)
;; will contain an incorrect value....
;bzo explain this better
;;

(defthmd wr-list-nil-to-clr-list
  (equal (wr-list ads nil ram)
         (clr-list ads ram))
  :hints (("goal" :in-theory (e/d (wr-list memory-clr)
                                  (wr==r!)))))

(defthm wr-list-equal-rewrite
  (implies (unique ads)
           (equal (equal (wr-list ads vals ram1) ram2)
                  (and (equal (my-wfixlist (len ads) vals) 
                              (rd-list ads ram2))
                       (equal (clr-list ads ram1)
                              (clr-list ads ram2)))))
  :hints (("Goal" :use (:instance wr-list-of-what-was-already-there-cheap (ram ram2))
           :in-theory (e/d (wr-list-nil-to-clr-list clr-list)
                           (wr-list-of-what-was-already-there
                            wr-list-of-what-was-already-there-cheap)))))



