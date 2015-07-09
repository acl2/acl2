; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility
(error "Is anyone using this?  If so please remove this error.")

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; lists-definitions.lisp
;; John D. Powell
;(in-package "LISTS")

;;
;; This file isolates lists definitions and types. The file currently
;; contains the following ACL2 constructs as they occur in the lists book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

;We make our own mv-nth function, so that we can disable it without getting theory warnings
;about how mv-nth cannot be completely disabled (since it is built-in in a deep way).
(defund val (n l)
  (declare (xargs :guard (and (integerp n)
                              (>= n 0)
                              (true-listp l))))
  (mv-nth n l))

(defthm mv-nth-to-val
  (equal (mv-nth n l)
         (val n l))
  :hints (("Goal" :in-theory (enable val))))

(defthm val-of-cons
  (equal (val n (cons a l))
         (if (zp n)
             a
           (val (+ -1 n) l)))
  :hints (("Goal" :in-theory (e/d (val) ( mv-nth-to-val)))))

(local (in-theory (e/d (len-of-cdr) (len))))

(in-theory (disable nth update-nth))

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

(defthm memberp-of-repeat-same
  (equal (memberp v (repeat n v))
         (not (zp n)))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm memberp-of-repeat
  (equal (memberp x (repeat n v))
         (and (equal x v)
              (integerp n)
              (< 0 n)))
  :hints (("Goal" :in-theory (enable repeat))))

;; We'll use MEMBERP instead of MEMBER in our reasoning from now on.  (Since
;; MEMBER doesn't always return a boolean, many of its rules must be IFF
;; rules. Since MEMBERP always returns a boolean, the analogous rules for it
;; can be EQUAL rules.)

(defund memberp (a x)
  (declare (type t a x))
  (if (consp x)
      (if (equal a (car x))
          t
        (memberp a (cdr x)))
    nil))

;; There are several functions similar to our memberp.  We rewrite all of the
;; others to ours (when they're used in a propositional context).
;;
;; Note: There was once some question as to whether or not having these rules
;; is a good idea.  But, I think we can make a strong case for preferring this
;; approach.  In particular, without these rules, we have many different
;; versions of the same function.  And, as a result, we would have to prove the
;; same theorems over and over in different equivalence contexts for each of
;; the different names.  It's quite likely that we would eventually forget one
;; and so forth.  By preferring memberp everywhere, we only need to write our
;; theorems about one function symbol.

(defthm member-is-memberp-propositionally
  (iff (member a x)
       (memberp a x))
  :hints(("Goal" :in-theory (enable memberp))))

(defthm member-equal-is-memberp-propositionally
  (iff (member-equal a x)
       (memberp a x))
  :hints(("Goal" :in-theory (enable memberp))))

(defthm member-eq-is-memberp-propositionally
  (iff (member-eq a x)
       (memberp a x))
  :hints(("Goal" :in-theory (enable memberp))))

(in-theory (disable member member-equal member-eq))

;; jcd - i think this should be enabled
(defthmd memberp-of-non-consp
  (implies (not (consp x))
           (equal (memberp a x)
                  nil))
  :hints (("Goal" :in-theory (enable memberp))))

;; jcd - i think memberp-of-non-consp should be enabled instead
(defthm memberp-of-non-consp-cheap
  (implies (not (consp x))
           (equal (memberp a x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable memberp))))

;; jcd - i think memberp-of-non-consp should be enabled instead
(defthm memberp-of-nil
  (equal (memberp a nil)
         nil)
  :hints (("goal" :in-theory (enable memberp))))

;; jcd - I don't see where it is disabled
;later disabled, since it introduces an IF
(defthm memberp-of-cons
  (equal (memberp a (cons b x))
         (if (equal a b)
             t
           (memberp a x)))
  :hints (("Goal" :in-theory (enable memberp))))

;; jcd - i think this is redundant
;non -cheap version?
(defthm memberp-of-cons-irrel
  (implies (not (equal a b))
           (equal (memberp a (cons b x))
                  (memberp a x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable memberp))))

;; jcd - i think this is redundant
;non -cheap version?
(defthm memberp-of-cons-reduce-cheap
  (implies (not (memberp a x))
           (equal (memberp a (cons b x))
                  (equal b a)))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints (("Goal" :in-theory (enable memberp))))

;When a and b are constants, the if test should always get resolved.
;So we probably always want this rule enabled. -ews
(defthm memberp-of-cons-cheap
  (implies (syntaxp (and (quotep a)
                         (quotep b)))
           (equal (list::memberp a (cons b x))
                  (if (equal a b)
                      t
                    (list::memberp a x)))))

(defthm memberp-car
  (equal (memberp (car x) x)
         (consp x)))

;; jcd - should we try this fc rule instead?
;;
;; (defthm memberp-of-cdr-forward-to-memberp
;;   (implies (memberp a (cdr x))
;;            (memberp a x))
;;   :rule-classes :forward-chaining)

;bzo expensive
;but maybe enable in the naive theory?
(defthmd memberp-of-cdr
  (implies (memberp a (cdr x))
           (memberp a x)))

(defthm memberp-of-cdr-cheap
  (implies (memberp a (cdr x))
           (memberp a x))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;; jcd - i don't like these rules and i'm removing them.

(defthmd memberp-when-not-memberp-of-cdr
  (implies (not (memberp a (cdr x)))
           (equal (memberp a x)
                  (if (consp x)
                      (equal a (car x))
                    nil)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct t
           :in-theory (enable memberp))))

;could try 0 for the backchain-limit
(defthm memberp-when-not-memberp-of-cdr-cheap
  (implies (not (memberp a (cdr x)))
           (equal (memberp a x)
                  (if (consp x)
                      (equal a (car x))
                    nil)))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))



;; jcd - try this theorem instead?
;;
;; (defthm member-of-cdr-when-not-car
;;   (implies (and (memberp a x)
;;                 (not (equal (car x) a)))
;;            (memberp a (cdr x))))

;hung on car... hang on (equal (car x) a)??
(defthmd memberp-and-not-cdr-implies-equality
  (implies (and (memberp a x)
                (not (memberp a (cdr x))))
           (equal (car x) a)))




(defthm memberp-of-append
  (equal (memberp a (append x y))
         (or (memberp a x) (memberp a y)))
  :hints (("Goal" :in-theory (enable append))))

;; jcd - this seems redundant
;make -alt version?
(defthmd memberp-of-append-irrel
  (implies (not (memberp a x))
           (equal (memberp a (append x y))
                  (memberp a y))))

;; jcd - this seems redundant
;make -alt version?
(defthm memberp-of-append-irrel-cheap
  (implies (not (memberp a x))
           (equal (memberp a (append x y))
                  (memberp a y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))



;; Jared's Additions

(defthm memberp-type-1
  (implies (not (consp x))
           (equal (memberp a x) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable memberp))))

(defthm memberp-of-nthcdr-forward-to-memberp
  (implies (memberp a (nthcdr n x))
           (memberp a x))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm member-of-firstn-forward-to-memberp
  (implies (memberp a (firstn n x))
           (memberp a x))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable firstn))))

(defthm memberp-from-memberp-of-cdr-cheap
  (implies (list::memberp a (cdr x))
           (list::memberp a x))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defund map-cons (a x)
  (declare (type t a x))
  (if (consp x)
      (cons (cons a (car x))
            (map-cons a (cdr x)))
    nil))

(defthm map-cons-type-1
  (implies (consp x)
           (consp (map-cons a x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable map-cons))))

(defthm map-cons-type-2
  (implies (not (consp x))
           (equal (map-cons a x)
                  nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable map-cons))))

(defthm consp-of-map-cons
  (equal (consp (map-cons a x))
         (consp x)))

(defthm map-cons-of-non-consp-two
  (implies (not (consp x))
           (equal (map-cons a x)
                  nil)))

(defthm map-cons-of-cons
  (equal (map-cons a (cons b x))
         (cons (cons a b)
               (map-cons a x)))
  :hints(("Goal" :in-theory (enable map-cons))))

(defthm car-of-map-cons
  (equal (car (map-cons a x))
         (if (consp x)
             (cons a (car x))
           nil)))

(defthm cdr-of-map-cons
  (equal (cdr (map-cons a x))
         (map-cons a (cdr x))))

(defthm len-of-map-cons
  (equal (len (map-cons a x))
         (len x)))

(defthm map-cons-of-append
  (equal (map-cons a (append x y))
         (append (map-cons a x)
                 (map-cons a y)))
  :hints(("Goal" :in-theory (enable append))))

(defthm firstn-of-map-cons
  (equal (firstn n (map-cons a x))
         (map-cons a (firstn n x)))
  :hints(("Goal" :in-theory (enable firstn))))

(defthm nthcdr-of-map-cons
  (equal (nthcdr i (map-cons a x))
         (map-cons a (nthcdr i x)))
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm memberp-of-map-cons
  (equal (memberp a (map-cons b x))
         (and (consp a)
              (equal (car a) b)
              (memberp (cdr a) x)))
  :hints(("Goal" :in-theory (enable map-cons))))

(defthm alistp-of-map-cons
  (alistp (map-cons a x))
  :hints(("Goal" :in-theory (enable map-cons))))


;; Note that we are using acl2::member here instead of list::memberp

(defthm member-append
  (iff (member x (append y z))
       (or (member x y)
           (member x z)))
  :hints (("Goal" :in-theory (enable member append))))

(defthm member-map-cons
  (iff (member x (map-cons y list))
       (and (consp x)
            (equal (car x) y)
            (member (cdr x) list)))
  :hints (("goal" :in-theory (enable member map-cons))))

(defun setequiv (x y)
  (and (subsetp x y)
       (subsetp y x)))

(defthm weak-right-normalization-cons
  (implies
   (memberp a x)
   (setequiv (cons a x) x)))

(defthm weak-right-normalization-append
  (implies
   (subsetp x y)
   (setequiv (append x y) y)))

(defthm weak-right-normalization-remove
  (implies
   (not (memberp a x))
   (equiv (remove a x) x)))

(defthm open-setequiv-on-not-consp
  (implies
   (not (consp x))
   (equal (setequiv x y)
          (not (consp y)))))

(in-theory (disable setequiv))

(defchoose setfix x (y)
  (setequiv x y)
  :strengthen t)

(defthm setequiv-implies-equal-setfix-1
  (implies (setequiv y y1)
           (equal (setfix y) (setfix y1)))
  :rule-classes (:congruence))

(defthm setfix-fixes
  (setequiv (setfix x) x))

(defund setfixed-p (x)
  (equal x (setfix x)))

(defthm setfixed-p-setfix
  (setfixed-p (setfix x)))

(defthm equal-setfix-to-setequiv
  (equal (equal (setfix x) y)
         (and (setfixed-p y)
              (setequiv x y))))

;does something like this function exist elsewhere?
(defun find-index (key lst)
  (if (endp lst)
      0
    (if (equal key (car lst))
        0
    (+ 1 (find-index key (cdr lst))))))


(defthm find-index-nth-0
  (equal (find-index (nth 0 x) x)
         0))


;bzo gen the 0 somehow?
(defthm memberp-nth-0-self
  (equal (memberp (nth 0 x) x)
         (consp x))
  :hints (("Goal" :in-theory (enable nth))))

;other way too?
(defthm len-cdr-compare-to-n-minus-one
  (implies (syntaxp (not (quotep n))) ;otherwise, this will match on (< '-1 (LEN (CDR x))).  disgusting.
           (equal (< (+ -1 n) (len (cdr x)))
                  (if (consp x)
                      (< n (len x))
                    (< n 1)))))

;; (thm
;;  (implies (bag::memberp key key-names)
;;           (equal (find-index key (cdr key-names))
;;                  (if (consp (cdr key-names))
;;                      (+ -1 (find-index key key-names))
;;                    0)))
;;  :hints (("Goal" :induct t
;;           :do-not '(generalize eliminate-destructors))))

(defthm find-index-when-not-memberp
  (implies (not (memberp key lst))
           (equal (find-index key lst)
                  (len lst))))


(in-theory (disable find-index))

(defthm memberp-nth
 (implies (< (nfix n) (len lst))
          (memberp (nth n lst) lst))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable nth ;bag::unique
                             MEMBERP-OF-CDR-CHEAP
                             ))))

(defthm find-index-of-car
  (equal (find-index (car key-names) key-names)
         0)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (find-index nth)
                           (;find-index-of-cdr
                            )))))

(defthm find-index-of-cons-same
  (equal (find-index item (cons item res))
         0)
  :hints (("Goal" :in-theory (e/d (find-index) (;FIND-INDEX-OF-CDR
                                                )))))

(defthm find-index-of-cons-diff
  (implies (not (equal item1 item2))
           (equal (find-index item1 (cons item2 res))
                  (+ 1 (find-index item1 res))))
  :hints (("Goal" :in-theory (e/d (find-index) (;FIND-INDEX-OF-CDR
                                                )))))

(defthm nth-of-find-index-of-car
  (implies (consp lst)
           (equal (nth (find-index (car lst) lst) lst)
                  (car lst)))
  :hints (("Goal" :in-theory (e/d (find-index) (;find-index-of-cdr
                                                      )))))

(defthm find-index-less-than-len
  (equal (< (find-index val lst) (len lst))
         (memberp val lst))
  :hints (("Goal" :in-theory (enable find-index))))

(defthm nth-of-find-index
  (implies (list::memberp val lst)
           (equal (nth (list::find-index val lst) lst)
                  val))
  :hints (("Goal" :in-theory (enable list::find-index))))

;; bzo (ews and jcd) We would like to disable true-listp as well, but we're
;; afraid it may break a lot of stuff, so we haven't tried it yet.

(in-theory (disable nthcdr append))

;; Note (jcd and ews): At one point, we tried strengthened this rule by moving
;; the consp hypothesis into the conclusion.  The modified rule was:
;;
;; (defthm equal-cons-cases
;;   (equal (equal (cons a b) c)
;;          (and (consp c)
;;               (equal a (car c))
;;               (equal b (cdr c)))))
;;
;; This rule turned out to be too strong.  It caused some proofs to fail, but
;; worse was the way that it slowed down proofs.  For example, bags/meta.lisp
;; originally took about 170 seconds, but using the new rule the time ballooned
;; to 1,200 seconds.  We have concluded that the original rule is what we
;; wanted, and so we have not changed the following:
; Hmmm.  Maybe the problem was that ACL2 unifies constant lists with cons?  Maybe a syntaxp test would help?  -ews

(defthm equal-cons-cases
  (implies (consp c)
           (equal (equal (cons a b) c)
                  (and (equal a (car c))
                       (equal b (cdr c))))))



;; As expected, ACL2 now has CONS-CAR-CDR, so we comment out all this stuff. -ews
;;
;; ;; bzo (ews and jcd) - This rule is inspired by the built in axiom
;; ;; car-cdr-elim.  We think that the case splitting version is better.  We have
;; ;; asked Matt Kaufmann to change ACL2 to provide the new rule instead, and
;; ;; he may change car-cdr-elim at some point in the future.
;; ;;
;; ;; So, when version 2.9.3 comes out, someone should check to see if this rule
;; ;; is now built in, and if so, remove this!

;; (defthm car-cdr-elim-better
;;   (equal (cons (car x) (cdr x))
;;          (if (consp x)
;;              x
;;            (cons nil nil))))

;; ;; Note that we leave the :elim rule enabled -- we only want to replace the
;; ;; rewrite rule because we don't really know how the elim rule works.

;; (in-theory (disable (:rewrite car-cdr-elim)))



;; (jcd) - Originally there was a backchaining limit here of 0.  I have taken
;; this out.  I think that trying to establish (not (consp x)) should be
;; fairly cheap usually, even if some backchaining is allowed to occur.  And,
;; unless things are dramatically slower, I think that removing the limit is
;; justified on the grounds that this is clearly a strong "progress making"
;; rule, and we will want to have it fire whenever possible.

(defthm true-listp-of-non-consp
  (implies (not (consp x))
           (equal (true-listp x)
                  (equal nil x))))


;; Note (jcd): We proved the following rule (trivially) and found that some
;; later proofs that use lists were *much* slower.  By *much*, what we mean
;; is, a jump from .46 seconds to 95 seconds.  We thought these looked like
;; nice rules, so we started tracing type-set to figure out what was going on.
;; It turns out, that there is a function called type-set-cons, that
;; automatically "knows" these rules at a really deep level.  So, there is
;; really no need to prove them at all.  Hence, we have removed them.  Don't
;; uncomment them unless you know what you are doing.

;;
;; (defthm true-listp-of-cons-type-prescription
;;   (implies (true-listp y)
;;            (true-listp (cons a y)))
;;   :rule-classes :type-prescription)
;;
;; (defthm not-true-listp-of-cons-type-prescription
;;   (implies (not (true-listp y))
;;            (not (true-listp (cons a y))))
;;   :rule-classes :type-prescription)


;; Note (jcd): Why would we prove this rule?  Isn't this built into ACL2 as
;; well?  It turns out that it isn't.  Here is an example script to convince
;; yourself of it.  The example goes through with our rule, but not without.
;; (Another way to prove it without our rule is to use cases for (true-listp
;; y), but our rule will prove it with no hints.)
;;
;; (defstub foo (x) t)
;;
;; (in-theory (disable true-listp))

(defthm true-listp-of-cons
  (equal (true-listp (cons a y))
         (true-listp y))
  :hints(("Goal" :in-theory (enable true-listp))))

(defthm cdr-does-nothing-rewrite
  (equal (equal x (cdr x))
         (equal x nil)))

;bzo (ews and jcd) -  consider disabling this.
(defthm equal-car-differential
  (implies (and (not (equal a b))
                (equal (cdr a) (cdr b))
                (consp a)
                (consp b))
           (equal (equal (car a) (car b))
                  nil)))

;; Len-len-induction
;;
;; This is a useful induction scheme for cdr'ing down two lists at the same
;; time.  It is particularly helpful when you are trying to prove congruence
;; rules and need to recur down two lists x and x-equiv at the same time.

;; bzo (jcd) This should this be called cdr-cdr-induction, since it doesn't
;; mention len.  This is a really common induction scheme and it's used in many
;; books.  Renaming it will be some work.

(defun len-len-induction (x y)
  (if (and (consp x)
           (consp y))
      (len-len-induction (cdr x) (cdr y))
    nil))



;; finalcdr Function
;;
;; finalcdr keeps taking cdrs of X until we hit an atom, and returns that
;; atom.  For a true-listp, that atom will be nil, otherwise it will be
;; whatever is in the cdr-most position of the non true-list.

(defund finalcdr (x)
  (declare (type t x))
  (if (consp x)
      (finalcdr (cdr x))
    x))

(defthm finalcdr-when-true-listp
  (implies (true-listp x)
           (equal (finalcdr x)
                  nil))
  :hints (("Goal" :in-theory (enable finalcdr))))

(defthm finalcdr-when-non-consp
  (implies (not (consp x))
           (equal (finalcdr x)
                  x))
  :hints (("Goal" :in-theory (enable finalcdr))))

;bzo trying without this
;; (defthm finalcdr-when-cdr-not-consp
;;   (implies (and (consp x)
;;                 (not (consp (cdr x))))
;;            (equal (finalcdr x)
;;                   (cdr x)))
;;  :hints (("Goal" :in-theory (enable finalcdr))))

(defthm finalcdr-of-cdr
  (equal (finalcdr (cdr y))
         (if (consp y)
             (finalcdr y)
           nil))
  :hints (("Goal" :in-theory (enable finalcdr))))

(defthm acl2-count-of-finalcdr-linear
  (implies (consp y)
           (< (acl2-count (finalcdr y))
              (acl2-count y)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable finalcdr))))

(defthm acl2-count-finalcdr-less-than-acl2-count
  (equal (< (acl2-count (finalcdr y))
            (acl2-count y))
         (consp y)))

(defthm finalcdr-of-cons
  (equal (finalcdr (cons a x))
         (finalcdr x))
  :hints (("Goal" :in-theory (enable finalcdr))))

(defthm finalcdr-does-nothing-rewrite
  (equal (equal (finalcdr x) x)
         (not (consp x))))

(defthm finalcdr-append
  (equal (finalcdr (append a b))
         (finalcdr b))
  :hints (("Goal" :in-theory (enable append))))

;; fix Function
;;
;; fix changes the final cdr of X to be nil.  Many functions which operate
;; on lists (like the bags functions?) don't access those final cdrs and so are
;; unaffected if we call fix on their arguments.

(defund fix (x)
  (declare (type t x))
  (if (consp x)
      (cons (car x)
            (fix (cdr x)))
    nil))

(defthm fix-iff-consp
  (iff (fix x)
       (consp x))
  :hints (("Goal" :in-theory (enable fix))))

(defthm fix-of-non-consp
  (implies (not (consp x))
           (equal (fix x)
                  nil)))

(defthm fix-of-cons
  (equal (fix (cons a y))
         (cons a (fix y)))
  :hints (("Goal" :in-theory (enable fix))))

(defthm true-listp-fix
  (implies (true-listp x)
           (equal (fix x)
                  x))
  :hints (("Goal" :in-theory (enable fix))))

(defthm fix-does-nothing-rewrite
  (equal (equal x (fix x))
         (true-listp x)))

(defthm acl2-count-of-fix
  (equal (acl2-count (fix x))
         (- (acl2-count x)
            (acl2-count (finalcdr x))))
  :hints (("Goal" :in-theory (enable fix finalcdr))))



;; equiv Relation
;;
;; equiv: We say that two lists are congruent (i.e., equivalent) if their
;; fix's are the same, i.e., if they differ only in their final cdrs.  jcd
;; thinks this should be renamed to equiv, but maybe it's too much work now.

(defund equiv (x y)
  (declare (type t x y))
  (equal (fix x)
         (fix y)))

(defthm equal-of-fixes
  (equal (equal (fix x)
                (fix y))
         (equiv x y))
  :hints (("Goal" :in-theory (enable equiv))))

(local (in-theory (disable (:rewrite equal-of-fixes))))

(defthm fix-equiv
  (equiv (fix x)
             x)
  :hints(("Goal" :in-theory (enable equiv))))

(defthm finalcdr-equiv
  (equiv (finalcdr x)
             nil)
  :hints(("Goal" :in-theory (enable equiv))))

(defthm equiv-of-non-consp-two
  (implies (not (consp y))
           (equal (equiv x y)
                  (not (consp x))))
  :hints (("Goal" :in-theory (enable equiv))))

(defthm equiv-of-non-consp-one
  (implies (not (consp x))
           (equal (equiv x y)
                  (not (consp y))))
  :hints (("Goal" :in-theory (enable equiv))))

(defthm equiv-cons-cases
  (equal (equiv x (cons y z))
         (and (consp x)
              (equal y (car x))
              (equiv z (cdr x))))
  :hints (("Goal" :in-theory (enable equiv))))

(defthm equiv-of-two-true-listps
  (implies (and (true-listp x)
                (true-listp y))
           (equal (equiv x y)
                  (equal x y)))
  :hints (("Goal" :in-theory (enable equiv))))

;This looks like it could be expensive if k is large.
(defthm equiv-of-constant
  (implies (and (syntaxp (quotep k))
                (consp k))
           (equal (equiv k x)
                  (and (consp x)
                       (equal (car x) (car k))
                       (equiv (cdr x) (cdr k)))))
  :hints (("Goal" :in-theory (enable equiv fix))))

;bzo consider a recursive-flavored :definition rule instead?
;bzo consider disabling this?
(defthm open-equiv
  (implies (and (consp x)
                (consp y))
           (equal (equiv x y)
                  (and (equal (car x) (car y))
                       (equiv (cdr x) (cdr y)))))
  :hints (("Goal" :in-theory (enable equiv fix))))

(defthmd open-equiv-1
  (and
   (implies
    (consp x)
    (equal (equiv x y)
           (and (consp y)
                (equal (car x) (car y))
                (equiv (cdr x) (cdr y)))))
   (implies
    (consp y)
    (equal (equiv x y)
           (and (consp x)
                (equal (car x) (car y))
                (equiv (cdr x) (cdr y))))))
  :hints (("Goal" :in-theory (enable equiv fix))))

;; Len Theorems
;;
;; Despite being built into the system, ACL2 has few useful rules for reasoning
;; about len out of the box.  We add quite a few rules here.  We typically want
;; len to be disabled, but realizing that this is not the default, we have not
;; forced our will upon the user.  Note that if you disable len, you may wish
;; to also enable the :rewrite rule len-of-cdr.

;; bzo (ews and jcd) - We'd like to disable len at the top of the file but we
;; tried it and it seemed to break a lot in other libraries that use lists.
;; Revisit this later.

(local (in-theory (disable len)))

(defthm len-non-negative-linear
  (<= 0 (len x))
  :rule-classes :linear)

(defthm len-non-negative
  (equal (< (len x) 0)
         nil))

(defthm len-when-consp-linear
  (implies (consp x)
           (< 0 (len x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable len))))

(defthm len-pos-rewrite
  (equal (< 0 (len x))
         (consp x))
  :hints (("Goal" :in-theory (enable len))))

(defthm len-of-non-consp
  (implies (not (consp x))
           (equal (len x)
                  0))
  :hints (("Goal" :in-theory (enable len))))

(defthm len-equal-0-rewrite
  (equal (equal 0 (len x))
         (not (consp x)))
  :hints (("Goal" :in-theory (enable len))))


;; Note (jcd and ews): The rule below, consp-when-len-is-known-and-positive,
;; looks strange.  With it, we can prove the following:
;;
;; (defstub foo (x) t)
;;
;; (thm
;;  (implies (equal 2 (len x))
;;           (equal (foo (consp x))
;;                  (foo t))))
;;
;; Why have the free variable here?  Without it, the rule would only be
;; triggered by: (< 0 (len x)), but we want it to fire any time we know that
;; (len x) is equal to some term FOO (see whether FOO is known to be positive
;; and, if so, throw (consp x) into the type-alist).
;;
;; Why make this a :forward-chaining rule instead of a :rewrite rule?  Well, we
;; think that a :rewrite rule hung on (consp x) which all of a sudden starts
;; reasoning about len would be too expensive, although we guess we could make
;; this a :rewrite rule with a backchain-limit on the second hyp.  We haven't
;; looked into that yet.

(defthm consp-when-len-is-known-and-positive
  (implies (and (equal (len x) foo) ;foo is a free variable
                (< 0 foo))
           (consp x))
  :rule-classes :forward-chaining)

(defthm len-cons
  (equal (len (cons a x))
         (+ 1 (len x)))
  :hints (("Goal" :in-theory (enable len))))


;; Note (jcd): I thought for some time about combining the following rules,
;; since they are the same but have different rule classes.  In the end I
;; decided to leave them separate.  I think combining them would be okay in the
;; sense that you can always disable only the :linear or :rewrite portion of
;; the rule if you needed to.  However, generally people will just disable
;; "len-of-cdr" without specifying if the :linear or :rewrite portion is to be
;; used, and that would leave them without even the non-problematic and
;; potentially useful :linear version.  The split approach ensures that this
;; won't happen.

(defthm len-of-cdr-linear
  (implies (consp x)
           (equal (len (cdr x))
                  (+ -1 (len x))))
  :rule-classes :linear)

(defthmd len-of-cdr
  (implies (consp x)
           (equal (len (cdr X))
                  (+ -1 (len x)))))

;bzo replace the other one?
;should this be enabled?
(defthmd len-of-cdr-better
  (equal (len (cdr x))
         (if (consp x)
             (+ -1 (len x))
           0)))

(local (in-theory (enable len-of-cdr-better)))

(defthm len-of-cdr-bound-weak-linear
  (<= (len (cdr x))
      (len x))
  :rule-classes :linear)

(defthm len-of-cdr-bound-weak
  (equal (< (len x) (len (cdr x)))
         nil))

(defthm len-of-cdr-bound-tight-linear
  (implies (consp x)
           (< (len (cdr x))
              (len x)))
  :rule-classes :linear)

(defthm len-of-cdr-bound-tight
  (equal (< (len (cdr x)) (len x))
         (consp x)))

(defthm len-equal-1-rewrite
  (equal (equal (len y) 1)
         (equal (fix y) (list (car y))))
  :hints(("Goal" :in-theory (enable fix))))

;; Append Theorems
;;
;; As with len, few useful rules are built in for reasoning about append.  Here
;; we introduce a useful suite of such rules.  Also as with len, even though we
;; prefer to work with append disabled, we leave it enabled here since that is
;; the "default" behavior of ACL2.  Users are encouraged to disable append on
;; their own after including this book.

(defthm consp-append
  (equal (consp (append x y))
         (or (consp x)
             (consp y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-consp-type-one
  (implies (consp x)
           (consp (append x y)))
    :rule-classes ((:type-prescription)))

(defthm append-consp-type-two
  (implies (consp y)
           (consp (append x y)))
    :rule-classes ((:type-prescription)))

;; bzo (jcd): There was a comment that arithmetic/top-with-meta had a rule
;; named append-true-listp-type-prescription, and so the following rule was
;; named append-true-listp-type-prescription-better.  (Actually that rule comes
;; from meta/term-defuns.lisp, which is included by arithmetic/top-with-meta.)
;; The rule is inferior -- it has an additional hypothesis that (true-listp x).
;;
;; I've reported the problem to Matt Kaufmann, and I think he has fixed it in
;; the development version of 2.9.3.  Once 2.9.3 is released, we should see if
;; the theorem is fixed in those books.  Then, we might consider moving this
;; theorem to the ACL2:: package so that it will have the same name.
;; Otherwise, users might have to disable it in both packages (although it's
;; weird to want to disable a type prescription rule).

(defthm append-true-listp-type-prescription
  (implies (true-listp y)
           (true-listp (append x y)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable append))))

(defthm true-listp-of-append
  (equal (true-listp (append x y))
         (true-listp y))
  :hints (("Goal" :in-theory (enable append))))

(defthmd car-append
  (equal (car (append x y))
         (if (consp x)
             (car x)
           (car y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm car-append-not-consp
  (implies
   (not (consp x))
   (equal (car (append x y))
          (car y)))
  :hints (("goal" :in-theory (enable append))))

(defthm car-append-consp
  (implies
   (consp x)
   (equal (car (append x y))
          (car x)))
  :hints (("goal" :in-theory (enable append))))

(defthmd cdr-append
  (equal (cdr (append x y))
         (if (consp x)
             (append (cdr x) y)
           (cdr y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm cdr-append-not-consp
  (implies
   (not (consp x))
   (equal (cdr (append x y))
          (cdr y)))
  :hints (("goal" :in-theory (enable append))))

(defthm cdr-append-consp
  (implies
   (consp x)
   (equal (cdr (append x y))
          (append (cdr x) y)))
  :hints (("goal" :in-theory (enable append))))

(defthm len-append
  (equal (len (append x y))
         (+ (len x)
            (len y)))
  :hints (("Goal" :in-theory (enable append))))


(defthm equal-len-append
  (implies (and (true-listp x)
                (true-listp y)
                (equal (len x) (len y)))
           (equal (equal (append x p) (append y q))
                  (and (equal x y)
                       (equal p q))))
  :hints (("Goal"
           :in-theory (enable append)
           :induct (len-len-induction x y))))

;; TEMP (jcd) - removed this theorem because it is subsumed by
;; append-of-non-consp-one below.
;;
;; (defthm append-of-nil-one
;;   (equal (append nil x)
;;          x)
;;   :hints (("Goal" :in-theory (enable append))))

;; (jcd ) the -two version of this rule isn't easy to
;; state (if we append x onto a non-consp y, we change the final cdr of x to be
;; y)...  bzo make it anyway
(defthm append-of-non-consp-one
  (implies (not (consp x))
           (equal (append x y) y))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-iff
  (iff (append x y)
       (or (consp x) y))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-of-cons
  (equal (append (cons a x) y)
         (cons a (append x y)))
  :hints (("Goal" :in-theory (enable car-append cdr-append))))

(defthm equal-append-x-append-x
  (equal (equal (append x y)
                (append x z))
         (equal y z))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-associative
  (equal (append (append x y) z)
         (append x (append y z)))
  :hints (("Goal" :in-theory (enable append))))

;; TEMP (jcd) - A comment indicated that we don't need this rule if the
;; associativity of append is enabled, and I agree.  I have removed it.
;;
;; (defthm append-equality-cancel
;;   (equal (equal (append x y)
;;                 (append (append x z) w))
;;          (equal y (append z w))))

(defthm fix-of-append
  (equal (fix (append x y))
         (append x (fix y)))
  :hints (("Goal" :in-theory (enable fix append))))

(defthm append-of-nil-two
  (equal (append x nil)
         (fix x))
  :hints (("Goal" :in-theory (enable car-append fix))))

(defthm acl2-count-of-append-increases
  (implies (consp y)
           (< (acl2-count x)
              (acl2-count (append y x))))
  :hints (("Goal" :in-theory (disable acl2-count))))

(defthm append-equal-self-one
  (equal (equal x (append x y))
         (equal y (finalcdr x)))
  :hints (("Goal" :in-theory (enable append))))

;; TEMP (jcd) - removed this.  this is nothing more than an instance of the
;; equality axiom schema for functions, and it seems stupid to prove it.  It
;; was being used in the proof of append-equal-self-two below, but I've
;; replaced that with an explicit hint for how to do the proof.  At the least,
;; this should become a local event to the proof of append-equal-self-two.
;;
;; (defthm acl2-count-diff-means-not-equal
;;   (implies (< (acl2-count x) (acl2-count y))
;;            (not (equal x y))))

(defthm append-equal-self-two
   (equal (equal x (append y x))
          (not (consp y)))
   :hints(("Goal"
           :in-theory (disable acl2-count-of-append)
           :use (:instance acl2-count-of-append))))

(defthm appends-equal
  (equal (equal (append x1 y)
                (append x2 y))
         (equal (fix x1)
                (fix x2)))
  :hints (("Goal" :induct (len-len-induction x1 x2)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable append fix))))

(defthm append-equal-fix-rewrite
  (equal (equal (append x y) (fix x))
         (equal nil y))
  :hints (("Goal" :in-theory (enable append fix))))

;; TEMP (jcd) - originally we had the following rule, with a note asking if it
;; could be made more general:
;;
;; (defthm equiv-of-append-onto-finalcdr
;;   (equiv (append x (finalcdr y))
;;              x)
;;   :hints (("Goal" :in-theory (enable equiv))))
;;
;; I have removed it, since we already have the rule below, which is more
;; general and trivially implies equiv-of-append-onto-finalcdr with the
;; type prescription of finalcdr.

(defthm append-of-non-consp-2
  (implies (not (consp y))
           (equiv (append x y) x))
  :hints(("Goal" :in-theory (enable equiv fix))))

;; TEMP (jcd) -- I've replaced (equiv nil y) in the following rules with
;; (not (consp y)).  These are identical concepts, but (not (consp y)) seems
;; more primitive to me, and therefore seems to make "more" progress.

(defthm equiv-of-append-self-one
 (equal (equiv (append x y) x)
        (not (consp y)))
 :hints (("Goal" :in-theory (enable equiv fix))))

(defthm equiv-of-append-self-two
  (equal (equiv x (append x y))
         (not (consp y)))
  :hints (("Goal" :in-theory (enable equiv fix))))

(defthm equiv-of-append-self-three
  (equal (equiv (append y x) x)
         (not (consp y)))
  :hints (("Goal" :in-theory (enable equiv fix))))

(defthm equiv-of-append-self-four
  (equal (equiv x (append y x))
         (not (consp y)))
  :hints (("Goal" :in-theory (enable equiv fix))))

;make more like this?
(defthm equiv-of-two-append-same
  (equal (equiv (append x y)
                (append x z))
         (equiv y z))
  :hints (("Goal" :in-theory (enable equiv))))




;; Firstn Function
;;
;; Firstn is peculiar in that there are other libraries which use and define
;; it.  So, we have gone to some lengths to ensure that firstn is defined
;; entirely within the ACL2 package.

(defund firstn (ACL2::n ACL2::l)
  "The sublist of L consisting of its first N elements."
  (declare (xargs :guard (and (true-listp ACL2::l)
                              (integerp ACL2::n)
                              (<= 0 ACL2::n))))
  (cond ((endp ACL2::l) nil)
        ((zp ACL2::n) nil)
        (t (cons (car ACL2::l)
                 (firstn (1- ACL2::n) (cdr ACL2::l))))))

;; TEMP (jcd) added another test for the type prescription of firstn.

;; TEMP (jcd) - originally we had this rule (in nth-and-update-nth, maybe?),
;; but I've removed it because it is subsumed by firstn-of-zp
;;
;; (defthm firstn-0
;;   (equal (firstn 0 l)
;;          nil)
;;   :hints (("goal" :in-theory (enable firstn))))

(defthm firstn-of-zp
  (implies (zp n)
           (equal (firstn n x) nil))
  :hints (("Goal" :in-theory (enable firstn))))

;; TEMP (jcd) - this is a new rule, inspired by the list-defthms book.  Their
;; version applies to first-n-ac, but ours will apply to our firstn function.

(defthm consp-firstn
  (equal (consp (firstn n x))
         (and (not (zp n))
              (consp x)))
  :hints(("Goal" :in-theory (enable firstn))))

;; TEMP (jcd) - this is a new rule, inspired by the list-defthms book.  Their
;; version applies to first-n-ac, but ours will apply to our firstn function.

(defthm consp-firstn-type-prescription
  (implies (and (integerp n)
                (< 0 n)
                (consp x))
           (consp (firstn n x)))
  :rule-classes :type-prescription)


(defthm car-of-firstn
  (equal (car (firstn n y))
         (if (zp n)
             nil
           (car y)))
  :hints (("Goal" :in-theory (enable firstn))))

;; TEMP (jcd) - I found this rule buried in nth-and-update-nth.lisp, but
;; it seems like it belongs here.  (Probably has to do with the ACL2::firstn
;; versus LIST::firstn mess that we used to have).

(defthm firstn-cons
  (equal (firstn n (cons a b))
         (if (zp n)
             nil
           (cons a (firstn (1- n) b))))
  :hints (("Goal" :in-theory (enable firstn))))

(defthm firstn-iff
  (iff (firstn n x)
       (and (not (zp n))
            (consp x)))
  :hints (("Goal" :in-theory (enable firstn))))

(defthm len-of-firstn
  (equal (len (firstn n x))
         (min (nfix n) (len x)))
  :hints (("Goal" :in-theory (enable firstn))))

;; TEMP (jcd) - I am removing this rule in favor of firstn-does-nothing below,
;; which I believe should trivially subsume this.  (I rescued
;; firstn-does-nothing out of nth-and-update-nth.lisp)
;;
;; (defthm firstn-of-len-same
;;   (equal (firstn (len x) x)
;;          (fix x))
;;   :hints (("Goal" :in-theory (enable firstn len))))

(defthm firstn-does-nothing
  (implies (<= (len x) (nfix n))
           (equal (firstn n x)
                  (fix x)))
  :hints(("Goal" :in-theory (enable firstn))))

(defthm firstn-of-append
  (equal (firstn n (append x y))
         (append (firstn n x)
                 (firstn (+ n (- (len x))) y)))
  :hints (("Goal"
           :in-theory (enable firstn append fix))))

;; TEMP (jcd) - removed this rule on the grounds that firstn-of-append subsumes
;; it and, that, if (len x) is actually n above, then the rule will rewrite it
;; to (append (firstn (len x) x) nil) (with help from firstn-of-zp), which
;; append-of-nil-two will then rewrite to exactly (fix x), and we will
;; have achieved the same effect.  (In fact, I think this rule originally was
;; listed above firstn-of-append, so it wasn't getting the chance to fire)
;;
;; (defthm firstn-of-len-and-append-same
;;   (equal (firstn (len x) (append x y))
;;          (fix x))
;;   :hints (("Goal" :in-theory (enable firstn append))))

;; TEMP (jcd) - Removed this for now, seems like it's an obvious consequence of
;; the equality axiom schema for functions or whatever its called
;;
;; (defthmd not-equal-from-len-not-equal
;;   (implies (not (equal (len x) (len y)))
;;            (not (equal x y))))

;; TEMP (jcd) - Removed this appalling rule which doesn't seem to be necessary
;; anywhere for anything.
;;
;; (defthm equal-of-if-hack
;;   (implies (and (not (equal x y))
;;                 (not (equal x z)))
;;            (equal (equal x (if test y z))
;;                   nil)))

;Do we want to do something similar for (first 2 x)?  Probably not?  -ews
(defthm firstn-1-rewrite
  (implies (consp x)
           (equal (firstn 1 x)
                  (list (car x))))
  :hints (("Goal" :in-theory (enable firstn))))

(defthm list::firstn-1-rewrite-strong
  (equal (firstn 1 x)
         (if (consp x)
             (list (car x))
           nil))
  :hints (("Goal" :in-theory (enable firstn))))

(defthmd firstn-of-cdr
  (implies (natp n)
           (equal (firstn n (cdr lst))
                  (cdr (firstn (+ 1 n) lst)))))

(defthm cdr-of-firstn
  (implies (natp n)
           (equal (cdr (firstn n lst))
                  (firstn (+ -1 n) (cdr lst)))))

;; Nthcdr Function
;;
;; Like len and append, we prefer to keep nthcdr disabled, but we will only
;; locally disable it so that we do not force our will upon the user.

(local (in-theory (disable nthcdr)))


;; TEMP (jcd) -- made this rule more general.  it used to be the following:
;;
;; (defthm nthcdr-of-0
;;   (equal (nthcdr 0 x)
;;          x)
;;   :hints (("Goal" :in-theory (enable nthcdr))))

(defthm nthcdr-of-zp
  (implies (zp n)
           (equal (nthcdr n x)
                  x))
  :hints(("Goal" :in-theory (enable nthcdr))))

;; TEMP (jcd) -- rescued this rule from nth-and-update-nth.lisp

(defthm nthcdr-iff
  (implies (true-listp l)
           (iff (nthcdr n l)
                (< (nfix n) (len l))))
  :hints (("Goal" :in-theory (enable nthcdr))))

;; TEMP (jcd) -- added this type prescription rule.  previously it was a
;; rewrite rule.  also see true-listp-of-nthcdr directly below.

(defthm true-listp-of-nthcdr-type-prescription
  (implies (true-listp l)
           (true-listp (nthcdr n l)))
  :hints(("Goal" :in-theory (enable nthcdr)))
  :rule-classes :type-prescription)

;; TEMP (jcd) -- added this rewrite rule, which is new.  Previously we only
;; have the above type prescription rule, but as a :rewrite rule, and this
;; seems like it will be more effective because it has no hyps.

(defthm true-listp-of-nthcdr
  (equal (true-listp (nthcdr n l))
         (or (< (len l) (nfix n))
             (true-listp l)))
  :hints(("Goal" :in-theory (enable nthcdr))))


;; TEMP (jcd) - the rules car-nthcdr and cdr-nthcdr have been inspired by the
;; standard list-defthms book, but improved to remove hypotheses.

;; bzo (jcd) - do we really want car-nthcd?  It rewrites a term to
;; nth, but we haven't included the nth/update-nth book in this basic core!
;; For now I am going to say that this is ok, and hopefully if someone uses
;; this rule they will include the nth-and-update-nth.lisp book.  But, maybe
;; the answer is to extend the core with the basic theorems about nth which
;; do not mention update-nth.

(defthm car-nthcdr
  (equal (car (nthcdr n x))
         (nth n x))
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm cdr-nthcdr
  (equal (cdr (nthcdr n x))
         (nthcdr (1+ (nfix n)) x))
  :hints(("Goal" :in-theory (enable nthcdr))))


;; TEMP (jcd) -- Enabled this rule.  A comment asked if this rule was too
;; strong, but I think it is a good rule and unless it breaks things, I think
;; we will want to have it enabled.

(defthm nthcdr-of-cons
  (equal (nthcdr n (cons a x))
         (if (and (integerp n)
                  (< 0 n))
             (nthcdr (+ -1 n) x)
           (cons a x)))
  :hints(("Goal" :in-theory (enable nthcdr))))

;; TEMP (jcd) -- Removed these rules since I am enabling nthcdr-of-cons and
;; these are just special cases of it.  (These were disabled anyway)
;;
;; (defthmd nthcdr-of-cons-special-one
;;   (implies (syntaxp (quotep n))
;;            (equal (nthcdr n (cons a x))
;;                   (if (and (integerp n)
;;                            (< 0 n))
;;                       (nthcdr (+ -1 n) x)
;;                     (cons a x))))
;;   :hints(("Goal" :in-theory (enable nthcdr))))
;;
;; (defthmd nthcdr-of-cons-special-two
;;   (implies (syntaxp (quotep m))
;;            (equal (nthcdr (+ m n) (cons a x))
;;                   (if (and (integerp (+ m n))
;;                            (< 0 (+ m n)))
;;                       (nthcdr (+ (+ -1 m) n) x)
;;                     (cons a x))))
;;   :hints(("Goal" :in-theory (enable nthcdr))))


;; TEMP (jcd) - made this rule stronger.  originally it was the following:
;;
;; (defthm nthcdr-of-len
;;   (equal (nthcdr (len x) x)
;;          (finalcdr x))
;;   :hints (("Goal" :in-theory (enable nthcdr len))))

(defthm nthcdr-of-len-or-more
  (implies (<= (len path) (nfix n))
           (equal (nthcdr n path)
                  (if (equal (len path) (nfix n))
                      (finalcdr path)
                    nil)))
  :hints(("Goal" :in-theory (enable nthcdr))))


;; jcd - This rule originally asked "yuck?"  But I think it is actually a
;; nice rule.

(defthm nthcdr-of-non-consp
  (implies (not (consp x))
           (equal (nthcdr n x)
                  (if (zp n)
                      x
                    nil)))
  :hints (("Goal" :in-theory (enable nthcdr))))

;; (TEMP) jcd - Removed this rule because it is subsumed by nthcdr-append
;; below.  There was a comment here asking if we could generalize this.

;; (defthm nthcdr-of-len-and-append
;;   (equal (nthcdr (len p) (append p list))
;;          list)
;;   :hints (("Goal" :in-theory (enable nthcdr append))))

;; jcd - The following rule was essentially copied from the list-defthms
;; book.  It's a good rule.

(defthm nthcdr-of-append
  (equal (nthcdr n (append a b))
         (if (<= (nfix n) (len a))
             (append (nthcdr n a) b)
           (nthcdr (- n (len a)) b)))
  :hints(("Goal" :in-theory (enable nthcdr))))

;; jcd - Here's another nice rule from the list-defthms book that we didn't
;; have before.

(defthm nthcdr-of-firstn
  (equal (nthcdr i (firstn j x))
         (if (<= (nfix j) (nfix i))
             nil
           (firstn (- (nfix j) (nfix i)) (nthcdr i x))))
  :hints(("Goal" :in-theory (enable firstn nthcdr))))

(defthmd firstn-of-nthcdr
  (implies (and (natp m)
                (natp n))
           (equal (firstn m (nthcdr n s))
                  (nthcdr n (firstn (+ m n) s)))))

(defthm list::nthcdr-of-firstn-goes-to-nil
  (implies (<= (nfix j) (nfix i))
           (equal (nthcdr i (firstn j x))
                  nil))
  :hints (("Goal" :in-theory (enable firstn nthcdr))))


(defthm len-of-nthcdr
  (equal (len (nthcdr n l))
         (if (natp n) ; change to use nfix around n?
             (max 0 (- (len l) n))
           (len l)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm consp-of-nthcdr
  (equal (consp (nthcdr n l))
         (< (nfix n) (len l)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm fix-of-nthcdr
  (equal (fix (nthcdr n l))
         (nthcdr n (fix l)))
  :hints (("Goal" :in-theory (enable nthcdr fix))))

(defthm nthcdrs-agree-when-shorter-nthcdrs-agree
  (implies (and (equal (nthcdr m x) (nthcdr m y))
                (<= m n)
                (natp m)
                (natp n)
                )
           (equal (equal (nthcdr n y) (nthcdr n x))
                  t))
  :hints (("Goal" :in-theory (enable nthcdr))))


;; ======================================================
;;
;; list-fix-equiv: an equivalence for lists of lists
;; (most useful in the "path" library)
;;
;; ======================================================

(defun list::list-fix (list)
  (declare (type t list))
  (if (consp list)
      (cons (list::fix (car list)) (list::list-fix (cdr list)))
    nil))

(defthm true-list-listp-list-fix
  (true-list-listp (list::list-fix list)))

(defthm true-list-listp-implies-list-fix-identity
  (implies
   (true-list-listp list)
   (equal (list::list-fix list)
          list)))

(defthm open-list-fix
  (implies (consp list)
           (equal (list::list-fix list)
                  (cons (list::fix (car list)) (list::list-fix (cdr list))))))

(defthm iff-list-fix
  (iff (list::list-fix x)
       (consp x)))

(defthm consp-list-fix
  (equal (consp (list::list-fix x))
         (consp x)))

(defun list::list-equiv (x y)
  (equal
   (list::list-fix x)
   (list::list-fix y)))

(defthm open-list-equiv-nonconsp-1
  (implies
   (not (consp x))
   (equal
    (list::list-equiv x y)
    (not (consp y)))))

(defthm open-list-equiv-nonconsp-2
  (implies
   (not (consp y))
   (equal
    (list::list-equiv x y)
    (not (consp x)))))

(defthm open-list-equiv-consp-1
  (implies
   (consp x)
   (equal
    (list::list-equiv x y)
    (and
     (consp y)
     (equal
      (list::fix (car x))
      (list::fix (car y)))
     (list::list-equiv (cdr x) (cdr y))))))

(defthm open-list-equiv-consp-2
  (implies
   (consp x)
   (equal
    (list::list-equiv y x)
    (and
     (consp y)
     (equal
      (list::fix (car x))
      (list::fix (car y)))
     (list::list-equiv (cdr y) (cdr x))))))

(defthm list-equiv-list-fix-reduction
  (list::list-equiv (list::list-fix list) list))

(in-theory (disable list::list-equiv))

;; TEMP (jcd) - there was some question as to which way to go (push fix into
;; nthcdr, or pull it out?) but I think we want to use the rule above, since
;; the congruence for (nthcdr n l) will get us pretty far if all we care about
;; is list-equivalence.  I've commented out the already-disabled nthcdr-of-fix
;; below in the name of simplification.
;;
;; (defthmd nthcdr-of-fix
;;   (equal (nthcdr n (fix p))
;;          (fix (nthcdr n p))))

(defthm nthcdr-of-nthcdr
  (equal (nthcdr n1 (nthcdr n2 l))
         (nthcdr (+ (nfix n1) (nfix n2)) l))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm nthcdr-when-<=
  (implies (and (<= (len l) (nfix n))
                (true-listp l)
                )
           (equal (nthcdr n l)
                  nil))
  :hints (("Goal" :in-theory (enable nthcdr))))

;; TEMP (jcd) - rescued this theorem from nth-and-update-nth.lisp and also
;; changed it into rule-classes :linear instead of :rewrite.

(defthm acl2-count-of-nthcdr
  (implies (and (integerp n)
                (> n 0)
                (consp l))
           (< (acl2-count (nthcdr n l))
              (acl2-count l)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable nthcdr))))

;; TEMP (jcd) - added this rule which was inspired by list-defthms.lisp.  Our
;; rule uses equiv instead of equal, but we don't have a true-listp
;; hypothesis.

(defthm append-firstn-nthcdr
  (equal (append (firstn n l) (nthcdr n l))
         (if (<= (nfix n) (len l))
             l
           (fix l)))
  :hints(("Goal" :in-theory (enable firstn nthcdr))))



(defthmd equal-append-reduction!
  (equal (equal (append x y) z)
         (and (equiv x (firstn (len x) z))
              (equal y (nthcdr (len x) z))))
  :hints (("Goal"
           :induct (len-len-induction x z)
           :in-theory (enable firstn nthcdr append))))

;; TEMP (jcd) - rescued this rule from nth-and-update-nth.lisp

(defthm equal-append-append-simple
  (implies (equal (len a) (len b))
           (equal (equal (append a c)
                         (append b d))
                  (and (equal (fix a)
                              (fix b))
                       (equal c d))))
  :hints(("Goal" :in-theory (enable equiv
                                    equal-append-reduction!))))


;; TEMP (jcd) - removed this because now I haven't done anything to the local
;; theory and len-of-cdr is already set to be disabled when it is exported.
;;
;; (in-theory
;;  (e/d
;;   (len nthcdr firstn)
;;   (len-of-cdr)
;;   ))




;; Appendx.  The build in binary-append function has a guard which requires x
;; to be a true list.  This is sometimes irritating, so we provide the
;; following function which is provably equal to append logically, but which
;; removes the guard.  We use MBE so that the definition of appendx can just be
;; an "abbreviation rule" that expands to append.
;;
;; NOTE 1: You should NEVER try to write theorems about appendx; write your
;; theorems about "append" instead.
;;
;; NOTE 2: Using "appendx" will be much slower than "append", since surely Lisp
;; implementations will have a built in "native" append function, e.g., written
;; in C when using GCL, so if execution speed matters, you may prefer to use
;; "append" instead.

(defun binary-appendx (x y)
  (declare (type t x y))
  (mbe :logic (append x y)
       :exec (if (consp x)
                 (cons (car x) (binary-appendx (cdr x) y))
               y)))

;could phrase RHS in terms of len?
(defthm list-hack
  (equal (equal (list::fix x) (list (car x)))
         (and (consp x)
              (not (consp (cdr x))))))

(defthm list-equiv-hack
  (equal (equal (list::fix x) y)
         (and (true-listp y)
              (list::equiv x y))))

;make cheap version?
(defthm len-when-at-most-1
  (implies (not (consp (cdr x)))
           (equal (len x)
                  (if (consp x)
                      1
                    0))))

;;; need to sort these:

;generalize to subrange?
(defthm nthcdr-firstn-one-more
  (implies (and (natp n)
                (< n (len s))
                )
           (equal (nthcdr n (firstn (+ 1 n) s))
                  (list (nth n s))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (list::nthcdr-of-firstn ;nthcdr firstn (:definition nth)
                            )
                           (firstn-of-nthcdr)))))

;bzo might be expensive?
(defthm cars-match-from-firstn-fact
  (implies (and (equal x (firstn n y))
                (integerp n)
                (<= 0 n))
           (equal (equal (car x) (car y))
                  (if (consp x)
                      t
                    (equal nil (car y))))))

;bzo might be expensive?
(defthm cars-match-from-firstn-fact-2
  (implies (and (equal x (firstn n y))
                (integerp n)
                (<= 0 n))
           (equal (equal (car y) (car x))
                  (if (consp x)
                      t
                    (equal nil (car y))))))

;may be too strong for general use...
(defthmd list::equal-cons-cases-strong
  (equal (equal (cons a b) c)
         (and (consp c)
              (equal a (car c))
              (equal b (cdr c)))))

(defthmd len-cdr-equal-len-cdr-rewrite
  (equal (equal (len (cdr x)) (len (cdr y)))
         (if (consp x)
             (if (consp y)
                 (equal (len x) (len y))
               (equal 1 (len x))
               )
           (if (consp y)
               (equal 1 (len y))
             t)))
  :hints (("Goal" :in-theory (enable))))

(local (in-theory (disable acl2-count))) ;bzo would like this to be non-local?

(defthm acl2-count-of-cons
  (equal (acl2-count (cons x y))
         (+ 1 (acl2-count x) (acl2-count y)))
  :hints (("Goal" :in-theory (enable acl2-count))))

(defthm acl2-count-when-consp-linear
  (implies (consp x)
           (equal (acl2-count x)
                  (+ 1
                     (acl2-count (car x))
                     (acl2-count (cdr x)))))
  :rule-classes :linear)

;; ACL2-COUNT of CAR

(defthm acl2-count-of-car-bound-weak-linear
  (<= (acl2-count (car x))
      (acl2-count x))
  :rule-classes :linear)

(defthm acl2-count-of-car-bound-weak
  (equal (< (acl2-count x) (acl2-count (car x)))
         nil))

(defthm acl2-count-of-car-bound-tight
  (equal (< (acl2-count (car x)) (acl2-count x))
         (or (consp x)
             (< 0 (acl2-count x)))))

;; ACL2-COUNT of CDR

(defthm acl2-count-of-cdr-bound-weak-linear
  (<= (acl2-count (cdr x))
      (acl2-count x))
  :rule-classes :linear)

(defthm acl2-count-of-cdr-bound-weak
  (equal (< (acl2-count x) (acl2-count (cdr x)))
         nil))

(defthm acl2-count-of-cdr-bound-tight
  (equal (< (acl2-count (cdr x)) (acl2-count x))
         (or (consp x)
             (< 0 (acl2-count x)))))


;; ACL2-COUNT of NTH

(defthm acl2-count-of-nth-bound-weak-linear
  (<= (acl2-count (nth n l))
      (acl2-count l))
  :rule-classes :linear)

(defthm acl2-count-of-nth-bound-weak
  (equal (< (acl2-count l) (acl2-count (nth n l)))
         nil))

(defthm acl2-count-of-nth-bound-tight
  (equal (< (acl2-count (nth n l)) (acl2-count l))
         (or (consp l)
             (< 0 (acl2-count l)))))

(defthm acl2-count-of-nth-bound-tight-linear
  (implies (consp l)
           (< (acl2-count (nth n l)) (acl2-count l)))
  :rule-classes :linear)

(defun disjoint (x y)
  (declare (type t x y))
  (if (consp x)
      (if (memberp (car x) y)
          nil
        (disjoint (cdr x) y))
    t))

(defthm disjoint-remove-reduction-1
  (implies
   (not (memberp a y))
   (equal (disjoint (remove a x) y)
          (disjoint x y))))

(defthm open-disjoint-on-memberp
  (implies
   (memberp a x)
   (equal (disjoint x y)
          (and (not (memberp a y))
               (disjoint (remove a x) y)))))

(defthm not-consp-disjoint
  (implies
   (not (consp x))
   (equal (disjoint x y) t)))

(defthm disjoint-remove-definition
  (equal (disjoint x y)
         (if (consp x)
             (and (not (memberp (car x) y))
                  (disjoint (remove (car x) x) y))
           t))
  :rule-classes (:definition))

(defun mutual-non-membership (a x y)
  (implies
   (memberp a x)
   (not (memberp a y))))

(in-theory (disable disjoint-remove-reduction-1))
(in-theory (disable open-disjoint-on-memberp))

(defun unhide (x)
  (declare (type t x))
  x)

(defthm unhide-hide
 (equal (unhide (hide x))
     x)
 :hints (("Goal" :expand ((hide x)))))

(in-theory (disable unhide))

;n is a numeric value
;term is a nest of update-nths
;we return an equivalent nest that agrees with TERM for nth of n.
(defun drop-irrelevant-update-nth-calls-from-update-nth-nest-aux (n term changed-anything-flg)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term))
      (if changed-anything-flg term nil)
    (if (and (equal 'update-nth (car term))
             (quotep (cadr term))
             (natp (cadr (cadr term)))
             )
        (if (equal (cadr (cadr term)) ;strip off the quote
                   n)
            (if changed-anything-flg term nil) ;term ;could return the actual value?
          (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n (cadddr term) t))
      (if changed-anything-flg term nil))))

;; (defthm pseudo-termp-of-drop-irrelevant-update-nth-calls-from-update-nth-nest
;;   (implies (pseudo-termp term)
;;            (pseudo-termp (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n term))))

(defthm drop-irrelevant-update-nth-calls-from-update-nth-nest-aux-works-right
  (implies (and (natp n)
                (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n term flg))
           (equal (nth n (nth-update-nth-eval (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n term flg) alist))
                  (nth n (nth-update-nth-eval term alist))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;the function should return a flag if it doesn't do anything and in the case we shouldn't bother to build a new term?
;takes an nth term
(defun drop-irrelevant-update-nth-calls-from-update-nth-nest (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (consp (caddr term))
           (equal (car (caddr term)) 'update-nth) ;or else don't bother...
           (equal (car term) 'nth)
           (quotep (cadr term))
           (natp (cadr (cadr term)))
           )
      (let ((result (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux
                     (cadr (cadr term)) ;strip off the quote
                     (caddr term)
                     nil)))
        (if result
            `(nth ,(cadr term)
                  (unhide (hide ,result)))
          term))
    term))

(local (in-theory (disable update-nth)))

(defthm drop-irrelevant-update-nth-calls-from-update-nth-nest-meta-rule
  (equal (nth-update-nth-eval term alist)
         (nth-update-nth-eval (drop-irrelevant-update-nth-calls-from-update-nth-nest term) alist))
  :rule-classes ((:meta :trigger-fns (nth)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;;
;; :meta rule to quickly extract the nth component from a nest of update-nths
;; when the relevant indices are constants
;;

;n is a numeric value
;if this isn't going to make cause any change to the term, just return a flag?
(defun get-nth-component-of-update-nth-nest-aux (n term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term))
      nil
    (if (and (equal 'update-nth (car term))
             (quotep (cadr term))
             (natp (cadr (cadr term)))
             )
        (if (equal (cadr (cadr term)) ;strip off the quote
                   n)
            (caddr term)
          (get-nth-component-of-update-nth-nest-aux n (cadddr term)))
      nil)))

(defthm get-nth-component-of-update-nth-nest-aux-works-right
  (implies (and (get-nth-component-of-update-nth-nest-aux n term)
                (natp n))
           (equal (nth-update-nth-eval (get-nth-component-of-update-nth-nest-aux n term) alist)
                  (nth n (nth-update-nth-eval term alist))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;; (defthm pseudo-termp-of-get-nth-component-of-update-nth-nest
;;   (implies (pseudo-termp term)
;;            (pseudo-termp (get-nth-component-of-update-nth-nest-aux n term))))

(defun get-nth-component-of-update-nth-nest (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (consp (caddr term))
           (equal (car (caddr term)) 'update-nth) ;or else don't bother...
           (equal (car term) 'nth)
           (quotep (cadr term))
           (natp (cadr (cadr term)))
           )
      (let* ((val (get-nth-component-of-update-nth-nest-aux
                   (cadr (cadr term)) ;strip off the quote
                   (caddr term))))
        (if val
            `(unhide (hide ,val))
          term))
    term))

(defthm get-nth-component-of-update-nth-nest-meta-rule
  (equal (nth-update-nth-eval term alist)
         (nth-update-nth-eval (get-nth-component-of-update-nth-nest term) alist))
  :rule-classes ((:meta :trigger-fns (nth)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;The unhide/hide trick is from Robert Krug.
(defun unhide (x)
  (declare (type t x))
  x)

(defthm unhide-hide
  (equal (unhide (hide x))
         x)
  :hints (("Goal" :expand ((hide x)))))

(in-theory (disable unhide))

;n is a numeric value
;term is a nest of update-nths
;we return a term equivalent to (nth n term), either a value of an nth call on a simpler nest
(defun drop-irrelevant-update-nth-calls-from-update-nth-nest-aux (n term changed-anything-flg)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term))
      (if changed-anything-flg `(nth ',n (unhide (hide ,term))) nil)
    (if (and (equal 'update-nth (car term))
             (quotep (cadr term))
             (natp (cadr (cadr term)))
             )
        (if (equal (cadr (cadr term)) ;strip off the quote
                   n)
            `(unhide (hide ,(caddr term)))
          (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n (cadddr term) t)) ;set the flag
      (if changed-anything-flg `(nth ',n (unhide (hide ,term))) nil))))

;; (defthm pseudo-termp-of-drop-irrelevant-update-nth-calls-from-update-nth-nest
;;   (implies (pseudo-termp term)
;;            (pseudo-termp (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n term))))

(defthm drop-irrelevant-update-nth-calls-from-update-nth-nest-aux-works-right
  (implies (and (natp n)
                (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n nest flg))
           (equal (nth-update-nth-eval (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n nest flg) alist)
                  (nth n (nth-update-nth-eval nest alist))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;the function should return a flag if it doesn't do anything and in the case we shouldn't bother to build a new term?
;takes an nth term
(defun drop-irrelevant-update-nth-calls-from-update-nth-nest (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (consp (caddr term))
           (equal (car (caddr term)) 'update-nth) ;or else don't bother...
           (equal (car term) 'nth)
           (quotep (cadr term))
           (natp (cadr (cadr term)))
           )
      (let ((result (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux
                     (cadr (cadr term)) ;strip off the quote
                     (caddr term)
                     nil)))
        (if result
            result
          term))
    term))

(local (in-theory (disable update-nth)))

(defthm drop-irrelevant-update-nth-calls-from-update-nth-nest-meta-rule
  (equal (nth-update-nth-eval term alist)
         (nth-update-nth-eval (drop-irrelevant-update-nth-calls-from-update-nth-nest term) alist))
  :rule-classes ((:meta :trigger-fns (nth)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm remove-equal-reduction
  (equal (remove-equal a x)
         (remove a x)))

(defthm remove-remove
  (equal (remove a (remove b x))
         (remove b (remove a x))))

(defthm remove-cons
  (equal (remove a (cons b x))
         (if (equal a b)
             (remove a x)
           (cons b (remove a x)))))

(defthm remove-append
  (equal (remove x (append a b))
         (append (remove x a)
                 (remove x b))))

(defthm non-increasing-remove
  (<= (acl2-count (remove a x)) (acl2-count x)))

(defthm decreasing-remove
  (implies
   (list::memberp a x)
   (< (acl2-count (remove a x)) (acl2-count x)))
  :rule-classes (:linear))

(defthm memberp-remove
  (equal (memberp a (remove b x))
         (if (equal a b) nil
           (memberp a x))))

(defthm remove-reducton
  (implies
   (not (memberp a x))
   (equal (remove a x)
          (fix x))))

(defthm subset-remove-reduction-2
  (implies
   (not (memberp a x))
   (equal (subsetp x (remove a y))
          (subsetp x y))))

(defthm subset-remove-reduction-1
  (implies
   (memberp a y)
   (equal (subsetp (remove a x) y)
          (subsetp x y))))

;;
;; remove-list : a means of removing multiple elements of a list
;;

(defun remove-list (x y)
  (if (consp x)
      (remove (car x) (remove-list (cdr x) y))
    y))

(defthm remove-list-remove
  (equal (remove-list x (remove a y))
         (remove a (remove-list x y))))

(defthm remove-list-remove-list
  (equal (remove-list a (remove-list b x))
         (remove-list b (remove-list a x))))

(defthm remove-list-cons-1
  (equal (remove-list (cons a x) y)
         (remove a (remove-list x y))))

(defthm remove-list-cons-2
  (equal (remove-list x (cons a y))
         (if (memberp a x)
             (remove-list x y)
           (cons a (remove-list x y)))))

(defthm remove-list-append-1
  (equal (remove-list (append a b) x)
         (remove-list b (remove-list a x)))
  :hints (("Goal" :in-theory (enable append))))

(defthm remove-list-append-2
  (equal (remove-list a (append x y))
         (append (remove-list a x)
                 (remove-list a y))))

(defthm memberp-remove-list
  (equal (memberp a (remove-list x y))
         (if (memberp a x) nil
           (memberp a y))))

(defthm remove-list-remove-reduction-1
  (implies
   (not (memberp a y))
   (list::equiv (remove-list (remove a x) y)
                (remove-list x y))))

(defthm remove-list-remove-reduction-1-alt
  (implies
   (and
    (true-listp y)
    (not (memberp a y)))
   (equal (remove-list (remove a x) y)
          (remove-list x y))))

(defthm remove-list-remove-reduction-2
  (implies
   (memberp a x)
   (equal (remove-list x (remove a y))
          (remove-list x y))))

;;

(defthm remove-list-superset-reduction
  (implies
   (subsetp x y)
   (list::equiv (remove-list y x)
                nil)))

;;
;; Is this what we want to do?
;;

(defthm subsetp-cons-2
  (equal (subsetp x (cons a y))
         (subsetp (remove a x) y)))

(local
 (defthm memberp-append-fwd
   (implies
    (memberp a (append x y))
    (or (memberp a x)
        (memberp a y)))
   :rule-classes (:forward-chaining)))

(defthm subsetp-append-2
  (equal (subsetp x (append y z))
         (and (subsetp (remove-list y x) z)
              (subsetp (remove-list z x) y))))

(defthm subsetp-remove
  (subsetp (remove a x) x)
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((remove a x)))))

(defthm subsetp-remove-list
  (subsetp (remove-list a x) x)
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((remove-list a x)))))

(defthm superset-remove-list-id
  (equiv (remove-list x x) nil))

;; Rules that otherwise eliminate removes

(in-theory (disable subset-remove-reduction-2))
(in-theory (disable subset-remove-reduction-1))
(in-theory (disable remove-list-remove-reduction-2))
(in-theory (disable remove-list-remove-reduction-1-alt))
(in-theory (disable remove-list-remove-reduction-1))

(defun remove-induction-1 (x)
  (declare (xargs :measure (len x)))
  (if (consp x)
      (remove-induction-1 (remove (car x) x))
    x))

(defun remove-induction-2 (x y)
  (declare (xargs :measure (len x)))
  (if (consp x)
      (remove-induction-2 (remove (car x) x) (remove (car x) y))
    (list x y)))

(defun remove-induction-3 (x y z)
  (declare (xargs :measure (len x)))
  (if (consp x)
      (remove-induction-3 (remove (car x) x) (remove (car x) y) (remove (car x) z))
    (list x y z)))

(defthm memberp-from-consp-fwd
  (implies
   (consp x)
   (memberp (car x) x))
  :rule-classes (:forward-chaining))

(defthmd open-memberp-on-memberp
  (implies
   (memberp a list)
   (equal (memberp b list)
          (if (equal b a) t
            (memberp b (remove a list))))))

(defthm memberp-remove-definition
  (equal (memberp a x)
         (if (consp x)
             (or (equal a (car x))
                 (memberp a (remove (car x) x)))
           nil))
  :hints (("Goal" :in-theory (enable open-memberp-on-memberp)))
  :rule-classes (:definition))


(defthm open-subsetp-on-memberp
  (implies
   (memberp a x)
   (equal (subsetp x y)
          (and (memberp a y)
               (subsetp (remove a x) (remove a y))))))

(defthm subsetp-remove-definition
  (equal (subsetp x y)
         (if (consp x)
             (and (memberp (car x) y)
                  (subsetp (remove (car x) x) (remove (car x) y)))
           t))
  :hints (("Goal" :in-theory (disable SUBSET-BY-MULTIPLICITY)))
  :rule-classes (:definition))

(defthm open-remove-list-on-memberp
  (implies
   (memberp a x)
   (equal (remove-list x y)
          (remove-list (remove a x) (remove a y))))
  :hints (("Goal" :in-theory `(remove-list-remove-reduction-1-ALT
                               REMOVE-LIST-REMOVE-REDUCTION-2
                               MEMBERP-REMOVE
                               (:TYPE-PRESCRIPTION MEMBERP)
                               (:TYPE-PRESCRIPTION REMOVE)
                               ))))

(defthm remove-list-remove-definition
  (equal (remove-list a x)
         (if (consp a)
             (remove (car a) (remove-list (remove (car a) a) x))
           x))
  :rule-classes (:definition))

(in-theory (disable remove remove-list subsetp memberp))

;; bzo (jcd) - consider disabling repeat

(defund repeat (n v)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (cons v (repeat (1- n) v))))

(defthm repeat-zp
  (implies (zp n)
           (equal (repeat n v)
                  nil))
  :hints(("Goal" :in-theory (enable repeat))))

;; TEMP (jcd) - the following are two new rules inspired by list-defthms.lisp.

(defthm consp-repeat
  (equal (consp (repeat n v))
         (not (zp n)))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm consp-repeat-type-prescription
  (implies (and (integerp n)
                (< 0 n))
           (consp (repeat n v)))
  :rule-classes :type-prescription)

(defthm repeat-iff
  (iff (repeat n v)
       (not (zp n))))

(defthm car-repeat
  (equal (car (repeat n v))
         (if (zp n)
             nil
           v))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm cdr-repeat
  (equal (cdr (repeat n v))
         (if (zp n)
             nil
           (repeat (1- n) v)))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm len-repeat
  (equal (len (repeat n v))
         (nfix n))
  :hints(("Goal" :in-theory (enable repeat))))

(local (defun double-sub1-induct (n1 n2)
         (if (not (zp n1))
             (double-sub1-induct (1- n1) (1- n2))
           n2)))

(defthm equal-repeat-simple
  (equal (equal (repeat n v) nil)
         (zp n)))

(defthm equal-repeat-cons
  (equal (equal (repeat n v) (cons v2 x))
         (and (equal v v2)
              (< 0 (nfix n))
              (equal (repeat (1- n) v) x)))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm equal-repeat-repeat
  (equal (equal (repeat n v) (repeat n2 v2))
         (and (equal (nfix n) (nfix n2))
              (or (zp n) (equal v v2))))
  :hints (("Goal" :in-theory (enable repeat)
           :induct (double-sub1-induct n n2))))

(defthm firstn-repeat
  (equal (firstn n (repeat n2 v))
         (repeat (min (nfix n) (nfix n2)) v))
  :hints (("Goal" :in-theory (enable repeat)
           :induct (double-sub1-induct n n2))))

;; Here's a rule inspired by the list-defthms book, which shows what
;; happens when nthcdr is applied to repeat.

(defthm nthcdr-repeat
  (equal (nthcdr i (repeat j v))
         (if (<= (nfix j) (nfix i))
             nil
           (repeat (- (nfix j) (nfix i)) v)))
  :hints(("Goal" :in-theory (enable repeat)
          :induct (double-sub1-induct i j))))

(defthm append-of-repeat-and-repeat-same-val
  (implies (and (force (natp n))
                (force (natp m)))
           (equal (append (repeat n val) (repeat m val))
                  (repeat (+ m n) val)))
  :hints (("Goal" :in-theory (enable append repeat))))

;bzo gen the (list k) to (cons k rest) ?
(defthm append-repeat-singleton-same
  (equal (append (repeat n k) (list k))
         (repeat (+ 1 (nfix n)) k))
  :hints (("Goal" :in-theory (e/d (LIST::EQUAL-APPEND-REDUCTION!)
                                  ()))))

(defun setequiv (x y)
  (and (subsetp x y)
       (subsetp y x)))

(defthm setequiv-cons-commute
  (setequiv (cons a (cons b x))
            (cons b (cons a x))))

(defthm setequiv-remove-cons-duplicates
  (setequiv (cons a (cons a b))
            (cons a b)))

(defthm setequiv-append-commute
  (setequiv (append x (append y z))
            (append y (append x z))))

(defthm setequiv-remove-append-duplicates
  (setequiv (append x (append x y))
            (append x y)))

(defthm weak-right-normalization-cons
  (implies
   (memberp a x)
   (setequiv (cons a x) x)))

(defthm weak-right-normalization-append
  (implies
   (subsetp x y)
   (setequiv (append x y) y)))


;; This should move to the "remove" file.
(defthm weak-right-normalization-remove
  (implies
   (not (memberp a x))
   (equiv (remove a x) x)))

(defthmd existential-setequiv-reduction
  (equal (setequiv x y)
         (and (equal (memberp a x) (memberp a y))
              (setequiv (remove a x) (remove a y)))))

(defthm open-setequiv-on-not-consp
  (implies
   (not (consp x))
   (equal (setequiv x y)
          (not (consp y)))))

(in-theory (disable setequiv))

(defthmd open-setequiv-on-memberp
  (implies
   (memberp a y)
   (equal (setequiv x y)
          (and (memberp a x)
               (setequiv (remove a x) (remove a y)))))
  :hints (("Goal" :use existential-setequiv-reduction)))

(defthm setequiv-remove-definition
  (equal (setequiv x y)
         (if (consp x)
             (and (memberp (car x) y)
                  (setequiv (remove (car x) x) (remove (car x) y)))
           (not (consp y))))
  :hints (("Goal" :in-theory (enable open-setequiv-on-memberp)))
  :rule-classes (:definition))

(defthm setequiv-append-reduction-1
  (equal (setequiv (append x y) z)
         (and (subsetp x z)
              (setequiv (remove-list x y) (remove-list x z))))
  :hints (("Goal" :use (:instance open-setequiv-on-subsetp
                                  (a x)
                                  (x (append x y))
                                  (y z)))))

(defchoose setfix x (y)
  (setequiv x y)
  :strengthen t)

(defthm setequiv-implies-equal-setfix-1
  (implies (setequiv y y1)
           (equal (setfix y) (setfix y1)))
  :hints (("Goal" :use (:instance setfix (acl2::y1 y1))))
  :rule-classes (:congruence))

(defthm setfix-fixes
  (setequiv (setfix x) x)
  :hints (("Goal" :use ((:instance setfix (y x))))))

(defund setfixed-p (x)
  (equal x (setfix x)))

(defthm setfixed-p-setfix
  (setfixed-p (setfix x))
  :hints (("Goal" :in-theory (enable setfixed-p))))

(defthm setfixed-p-setfix-reduction
  (implies
   (setfixed-p x)
   (equal (setfix x) x))
  :hints (("Goal" :in-theory (enable setfixed-p))))

(defthm equal-setfix-to-setequiv
  (equal (equal (setfix x) y)
         (and (setfixed-p y)
              (setequiv x y)))
  :hints (("Goal" :in-theory (enable setfixed-p setequiv-setfix-reduction))))

;;
;; Pick-a-point for setequiv
;;

(defthm setequiv-append-swap
  (setequiv (append x y)
            (append y x)))

(defthm append-cons-commute
  (list::setequiv (append x (cons a y))
                  (cons a (append x y))))

;;
;; We could use definition rules for this .. (??)
;;
(defthmd open-setequiv-on-consp-1
  (implies
   (consp x)
   (equal (list::setequiv x y)
          (and (list::memberp (car x) y)
               (list::setequiv (remove (car x) x) (remove (car x) y)))))
  :hints (("Goal" :in-theory (enable list::setequiv))))

(defthm subsetp-cons-1
  (equal (subsetp (cons a x) y)
         (and (memberp a y)
              (subsetp x y))))

(defthm subsetp-append-1
  (equal (subsetp (append x y) z)
         (and (subsetp x z)
              (subsetp y z))))

(defthm subset-membership-free-subsetp
  (implies
   (and
    (subsetp x y)
    (memberp a x))
   (memberp a y))
  :rule-classes (:rewrite :forward-chaining))

(defthm subset-membership-free-memberp
  (implies
   (and
    (memberp a x)
    (subsetp x y))
   (memberp a y))
  :rule-classes (:rewrite :forward-chaining))


(defthm subset-chaining-1
  (implies
   (and
    (subsetp x y)
    (subsetp y z))
   (subsetp x z))
  :rule-classes (:rewrite :forward-chaining))

(defthm subset-chaining-2
  (implies
   (and
    (subsetp x y)
    (subsetp z x))
   (subsetp z y))
  :rule-classes (:rewrite :forward-chaining))

(defthm subsetp-not-consp-1
  (implies
   (not (consp x))
   (subsetp x y)))

(defthm subsetp-not-consp-2
  (implies
   (not (consp y))
   (equal (subsetp x y)
          (not (consp x)))))

(defthm subsetp-id
  (subsetp x x))

(defthm equal-subsetp-reduction-1
  (equal (equal (subsetp x y) z)
         (and
          (booleanp z)
          (implies
           (subsetp x y)
           z)
          (implies
           z
           (subsetp x y)))))

(defthm equal-subsetp-reduction-2
  (equal (equal z (subsetp x y))
         (and
          (booleanp z)
          (implies
           (subsetp x y)
           z)
          (implies
           z
           (subsetp x y)))))

(local (in-theory (disable UPDATE-NTH-EQUAL-REWRITE
                           UPDATE-NTH-EQUAL-UPDATE-NTH-REWRITE))) ;bzo why?

(defthm true-listp-update-nth-array
  (implies (true-listp l)
           (true-listp (update-nth-array n i v l)))
  :rule-classes :type-prescription)

(defthm true-listp-update-nth-array-rewrite
  (implies (true-listp l)
           (true-listp (update-nth-array n i v l))))
;; Theorems about Update-Nth-Array

(local (in-theory (disable update-nth-array)))

(defthm firstn-update-nth-array
  (implies (and (integerp n)
                (<= 0 n)
                (integerp n2)
                (<= 0 n2))
           (equal (firstn n (update-nth-array n2 i v l))
                  (if (<= n n2)
                      (append (firstn n l) (repeat (- n (len l)) nil))
                    (update-nth-array n2 i v (firstn n l)))))
  :hints (("Goal" :in-theory (enable firstn update-nth-array))))

(defthm nthcdr-update-nth-array
  (implies (and (integerp n)
                (<= 0 n)
                (integerp n2)
                (<= 0 n2))
           (equal (nthcdr n (update-nth-array n2 i v l))
                  (if (< n2 n)
                      (nthcdr n l)
                    (update-nth-array (- n2 n) i v (nthcdr n l)))))
  :hints (("Goal" :in-theory (enable nthcdr update-nth-array))))



;bzo can we improve the phrasing of this using a clear operation? -ews
(defthm equal-update-nth-array-casesplit
  (implies (and (integerp n)
                (<= 0 n))
           (equal (equal (update-nth-array n i v l1) L2)
                  (and (equal (update-nth i v (nth n l1)) (nth n l2))
                       (< n (len l2))
                       (equal (firstn n (append l1 (repeat (- n (len l1)) nil))) (firstn n l2))
                       (equal (nthcdr (1+ n) l1) (nthcdr (1+ n) l2)))))
  :hints (("Goal" :in-theory (enable update-nth-array
                                     equal-update-nth-casesplit))))

(defthm equal-update-nth-array-update-nth-array
  (implies (and (integerp n)
                (<= 0 n)
                (equal (len l1) (len l2)))
           (equal (equal (update-nth-array n i v1 l1)
                         (update-nth-array n i v2 l2))
                  (and
                   (equal (update-nth i v1 (nth n l1))
                          (update-nth i v2 (nth n l2)))
                   (equal (firstn n l1)
                          (firstn n l2))
                   (equal (nthcdr (1+ n) l1)
                          (nthcdr (1+ n) l2)))))
  :hints (("Goal" :in-theory (enable equal-update-nth-casesplit
                                     update-nth-array))))

;; len-update-nth-better in fcp2k model
(defthm len-update-nth-array-better
  (equal (len (update-nth-array n i v l))
         (max (1+ (nfix n)) (len l)))
  :hints (("Goal" :in-theory (enable update-nth-array max))))


(defthm update-nth-array-update-nth-array-diff
  (implies (not (equal (nfix i1) (nfix i2)))
           (equal (update-nth-array i1 j1 v1
                                    (update-nth-array i2 j2 v2 l))
                  (update-nth-array i2 j2 v2
                                    (update-nth-array i1 j1 v1 l))))
  :rule-classes ((:rewrite :loop-stopper ((i1 i2))))
  :hints (("Goal" :in-theory (enable update-nth-array))))

(defthm update-nth-array-update-nth-diff
  (implies
   (not (equal (nfix i1) (nfix i2)))
   (equal (update-nth-array i1 j1 v1
                      (update-nth i2 v2 l))
          (update-nth i2 v2
                      (update-nth-array i1 j1 v1 l))))
  :rule-classes ((:rewrite :loop-stopper ((i1 i2))))
  :hints (("Goal" :in-theory (enable update-nth-array))))

(defthm update-nth-update-nth-array-diff
  (implies
   (not (equal (nfix i1) (nfix i2)))
   (equal (update-nth i1 v1
                      (update-nth-array i2 j2 v2 l))
          (update-nth-array i2 j2 v2
                      (update-nth i1 v1 l))))
  :rule-classes ((:rewrite :loop-stopper ((i1 i2))))
  :hints (("Goal" :in-theory (enable update-nth-array))))

(defthm update-nth-array-update-nth-array-same
  (and
   (implies
    (not (equal (nfix j1) (nfix j2)))
    (equal (update-nth-array i j1 v1 (update-nth-array i j2 v2 l))
           (update-nth-array i j2 v2 (update-nth-array i j1 v1 l))))
   (equal (update-nth-array i j1 v1 (update-nth-array i j1 v2 l))
          (update-nth-array i j1 v1 l)))
  :rule-classes ((:rewrite :loop-stopper ((j1 j2))))
  :hints (("Goal" :in-theory (enable update-nth-array))))
