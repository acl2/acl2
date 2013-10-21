;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "extended-subsets")
(include-book "mergesort")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(deflist ordered-list-listp (x)
  (ordered-listp x)
  :guard t)

(defprojection :list (mergesort-list x)
               :element (mergesort x)
               :guard t
               :nil-preservingp t)

(defthm ordered-list-listp-of-mergesort-list
  (equal (ordered-list-listp (mergesort-list x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))



(defthm superset-of-somep-of-mergesort-left
  (equal (superset-of-somep (mergesort a) x)
         (superset-of-somep a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm superset-of-somep-of-mergesort-list-right
  (equal (superset-of-somep a (mergesort-list x))
         (superset-of-somep a x))
  :hints(("Goal" :induct (cdr-induction x))))




(defund fast-superset-of-somep (a x)
  (declare (xargs :guard (and (ordered-listp a)
                              (ordered-list-listp x))))

; This is the same as superset-of-somep when A has already been mergesorted,
; and every member of X has already been mergesorted.  This gives us an O(n^2)
; version of superset-of-somep, instead of the O(n^3) performance when the
; ordinary subsetp operation is used.

  (if (consp x)
      (or (ordered-list-subsetp (car x) a)
          (fast-superset-of-somep a (cdr x)))
    nil))

(defthmd fast-superset-of-somep-when-not-consp
  (implies (not (consp x))
           (equal (fast-superset-of-somep a x)
                  nil))
  :hints(("Goal" :in-theory (enable fast-superset-of-somep))))

(defthmd fast-superset-of-somep-of-cons
  (equal (fast-superset-of-somep a (cons b x))
         (or (ordered-list-subsetp b a)
             (fast-superset-of-somep a x)))
  :hints(("Goal" :in-theory (enable fast-superset-of-somep))))

(defthm fast-superset-of-somep-removal
  (implies (force (and (ordered-listp a)
                       (ordered-list-listp x)))
           (equal (fast-superset-of-somep a x)
                  (superset-of-somep a x)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable fast-superset-of-somep-when-not-consp
                             fast-superset-of-somep-of-cons))))





(defund fast-remove-supersets1 (todo done todo-sorted done-sorted)
  (declare (xargs :guard (and (equal todo-sorted (mergesort-list todo))
                              (equal done-sorted (mergesort-list done)))))

; This is the same as remove-supersets1 given that the guard holds.  The
; todo-sorted and done-sorted lists act as caches so we don't have to
; repeatedly sort things.  We use fast-superset-of-somep, which is O(n^2),
; repeatedly, so that the total cost is O(n^3).  But this is still better than
; the O(n^4) behavior of remove-supersets1.

  (if (consp todo-sorted)
      (let ((candidate (car todo-sorted))
            (remaining (cdr todo-sorted)))
        (if (or (fast-superset-of-somep candidate remaining)
                (fast-superset-of-somep candidate done-sorted))
            (fast-remove-supersets1 (cdr todo)
                                    done
                                    (cdr todo-sorted)
                                    done-sorted)
          (fast-remove-supersets1 (cdr todo)
                                  (cons (car todo) done)
                                  (cdr todo-sorted)
                                  (cons (car todo-sorted) done-sorted))))
    (fast-rev done)))

(defthmd fast-remove-supersets1-when-not-consp
  (implies (not (consp todo-sorted))
           (equal (fast-remove-supersets1 todo done todo-sorted done-sorted)
                  (fast-rev done)))
  :hints(("Goal" :in-theory (enable fast-remove-supersets1))))

(defthmd fast-remove-supersets1-of-cons
  (equal (fast-remove-supersets1 todo done (cons a todo-sorted) done-sorted)
         (let ((candidate a)
               (remaining todo-sorted))
           (if (or (fast-superset-of-somep candidate remaining)
                   (fast-superset-of-somep candidate done-sorted))
               (fast-remove-supersets1 (cdr todo)
                                       done
                                       todo-sorted
                                       done-sorted)
             (fast-remove-supersets1 (cdr todo)
                                     (cons (car todo) done)
                                     todo-sorted
                                     (cons a done-sorted)))))
  :hints(("Goal" :in-theory (enable fast-remove-supersets1))))

(defthm fast-remove-supersets1-removal
  (equal (fast-remove-supersets1 todo done (mergesort-list todo) (mergesort-list done))
         (remove-supersets1 todo done))
  :hints(("Goal"
          :in-theory (enable (:induction remove-supersets1)
                             fast-remove-supersets1-when-not-consp
                             fast-remove-supersets1-of-cons)
          :induct (remove-supersets1 todo done))))



;; One minor thing is that because of arithmetic, it would be slightly expensive
;; to use a function such as len-at-leastp, below, to check the length of a list
;; against 250.
;;
;; (defund len-at-leastp (x n)
;;   (declare (xargs :guard (natp n)))
;;   (if (zp n)
;;       t
;;     (if (consp x)
;;         (len-at-leastp (cdr x) (- n 1))
;;       nil)))
;;
;; (defthm len-at-leastp-correct
;;   (equal (len-at-leastp x n)
;;          (<= n (len x)))
;;   :hints(("Goal" :in-theory (enable len-at-leastp))))
;;
;; Instead, we come up with a very specialized and funny-looking test.  This
;; is pretty gross, but it's considerably faster on some sample tests, shown
;; below.

(definlined cdr-10-times (x)
  (declare (xargs :guard t))
  (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr x)))))))))))

(definlined cdr-50-times (x)
  (declare (xargs :guard t))
  (let* ((10cdrs (and (consp x) (cdr-10-times x)))
         (20cdrs (and (consp 10cdrs) (cdr-10-times 10cdrs)))
         (30cdrs (and (consp 20cdrs) (cdr-10-times 20cdrs)))
         (40cdrs (and (consp 30cdrs) (cdr-10-times 30cdrs))))
    (and (consp 40cdrs)
         (cdr-10-times 40cdrs))))

(definlined cdr-250-times (x)
  (declare (xargs :guard t))
  (let* ((50cdrs  (cdr-50-times x))
         (100cdrs (cdr-50-times 50cdrs))
         (150cdrs (cdr-50-times 100cdrs))
         (200cdrs (cdr-50-times 150cdrs)))
    (cdr-50-times 200cdrs)))

(definlined len-over-250p (x)
  (declare (xargs :guard t))
  (consp (cdr-250-times x)))

;; We test the performance of the two functions with the following loop.
;;
;; (defparameter *test* nil)
;; (progn
;;   (setf *test*
;;         (loop for i fixnum from 1 to 251 collect i))
;;   (time (loop for i fixnum from 1 to 1000000
;;               do
;;               (MILAWA::len-overp *test* 250)))
;;   (time (loop for i fixnum from 1 to 1000000
;;               do
;;               (MILAWA::len-over-250p *test*)))
;;   nil)
;;
;; Test results are as follows.  Times in seconds.
;;
;;   Test size     Len-overp      Len-over-250p
;;   1             .04            .08
;;   2             .077           .086
;;   3             .11            .08
;;   10            .33            .08
;;   60            1.9            .33
;;   100           3.2            .52
;;   180           5.7            .91
;;   240           7.6            1.2
;;   251           7.9            1.2
;;
;; So, we're willing to put up with the ugliness to get this good performance.

(defund some-len-over-250p (x)
  ;; BOZO not used anymore.
  (declare (xargs :guard t))
  (if (consp x)
      (or (len-over-250p (car x))
          (some-len-over-250p (cdr x)))
    nil))


(defund fast-remove-supersets (x)
  (declare (xargs :guard t))
  ;; Is it worth it to mergesort?  Only if we're going to be doing a lot of
  ;; subset checks.  As a rough heuristic, we will mergesort when there are
  ;; more than 250 members in the list.  This improved a particularly egregious
  ;; call of remove-supersets1 in level10/fast-image.lisp, in a use of
  ;; %cleanup, from 327 to 199 seconds.  We may eventually want to revisit
  ;; this and think about other heuristics that could make better decisions.
  (if (len-over-250p x)
      (fast-remove-supersets1 x nil (mergesort-list x) nil)
    (remove-supersets x)))

(defthm fast-remove-supersets-removal
  (equal (fast-remove-supersets x)
         (remove-supersets x))
  :hints(("Goal"
          :in-theory (enable fast-remove-supersets remove-supersets)
          :use ((:instance fast-remove-supersets1-removal
                           (todo x)
                           (done nil))))))

