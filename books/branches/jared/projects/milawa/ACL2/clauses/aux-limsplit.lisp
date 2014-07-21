; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
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
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "aux-split")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund clause.aux-limsplit (todo done n)
  (declare (xargs :guard (and (logic.term-listp todo)
                              (logic.term-listp done)
                              (true-listp todo)
                              (natp n))
                  :verify-guards nil
                  :measure (clause.split-count-list todo)))
  (if (zp n)
      ;; This is a tricky, important ordering.  See the builder and its cutoff builder for
      ;; the messy details.
      (list (revappend done todo))
    (if (consp todo)
        (let* ((negativep (clause.negative-termp (car todo)))
               (guts      (if negativep (clause.negative-term-guts (car todo)) (car todo))))
          (cond

           ((and negativep (clause.negative-termp guts))
            ;; Cancel (not (not a))
            (clause.aux-limsplit (cons (clause.negative-term-guts guts) (cdr todo)) done
                                 ;; Don't decrement n -- we haven't split anything!
                                 n))

           ((and (logic.functionp guts)
                 (equal (logic.function-name guts) 'if)
                 (equal (len (logic.function-args guts)) 3))
            (let ((args (logic.function-args guts)))
              (if negativep
                  ;; The first literal is (not (if a b c)).
                  ;; New clause 1: (not a) v (not b) v rest
                  ;; New clause 2: a v (not c) v rest
                  (let ((a      (first args))
                        (not-a  (logic.function 'not (list (first args))))
                        (not-b  (logic.function 'not (list (second args))))
                        (not-c  (logic.function 'not (list (third args))))
                        (rest   (cdr todo)))
                    (let ((triv1 (clause.aux-split-trivial-branchp not-a not-b rest done))
                          (triv2 (clause.aux-split-trivial-branchp a not-c rest done)))
                      (cond ((and triv1 triv2)
                             nil)
                            (triv1
                             ;; Jared's guess.  We probably don't want to decrease n here, because
                             ;; even though we've split an if, one of the branches was trivial and
                             ;; so really we're still dealing with the same number of clauses as
                             ;; before.  So, this seems more to me like cancelling double negatives
                             ;; or normalizing nots or something, rather than actual splitting.
                             (clause.aux-limsplit (cons a (cons not-c rest)) done n))
                            (triv2
                             (clause.aux-limsplit (cons not-a (cons not-b rest)) done n))
                            (t
                             ;; But in the case where we really do split, decrease n!
                             (revappend (clause.aux-limsplit (cons not-a (cons not-b rest)) done (- n 1))
                                        (clause.aux-limsplit (cons a (cons not-c rest)) done (- n 1)))))))
                ;; The first literal is (if a b c).
                ;; New clause 1: (not a) v b v rest
                ;; New clause 2: a v c v rest
                (let ((a     (first args))
                      (not-a (logic.function 'not (list (first args))))
                      (b     (second args))
                      (c     (third args))
                      (rest  (cdr todo)))
                  (let ((triv1 (clause.aux-split-trivial-branchp not-a b rest done))
                        (triv2 (clause.aux-split-trivial-branchp a c rest done)))
                    (cond ((and triv1 triv2)
                           nil)
                          (triv1
                           (clause.aux-limsplit (cons a (cons c rest)) done n))
                          (triv2
                           ;; BOZO consider not decreasing n
                           (clause.aux-limsplit (cons not-a (cons b rest)) done n))
                          (t
                           (revappend (clause.aux-limsplit (cons not-a (cons b rest)) done (- n 1))
                                      (clause.aux-limsplit (cons a (cons c rest)) done (- n 1))))))))))

           (t
            ;; We can't split this literal, but we'll normalize it to "(not x)" if it is
            ;; some other negative-termp variant of not.
            (clause.aux-limsplit (cdr todo)
                                 (cons (if negativep
                                           (logic.function 'not (list guts))
                                         (car todo))
                                       done)
                                 ;; Don't decrement n -- we haven't split anything!
                                 n))))
      (list done))))

(encapsulate
 ()
 (local (in-theory (enable clause.aux-limsplit)))

 (defthm true-listp-of-clause.aux-limsplit
   (implies (force (true-listp todo))
            (equal (true-listp (clause.aux-limsplit todo done n))
                   t)))

;;  (defthm consp-of-clause.aux-limsplit
;;    (implies (force (true-listp todo))
;;             (equal (consp (clause.aux-limsplit todo done n))
;;                    t)))

;;  (defthm clause.aux-limsplit-under-iff
;;    (implies (force (true-listp todo))
;;             (iff (clause.aux-limsplit todo done n)
;;                  t)))

 (defthm forcing-term-list-listp-of-clause.aux-limsplit
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (true-listp todo)))
            (equal (logic.term-list-listp (clause.aux-limsplit todo done n))
                   t)))

 (defthm forcing-term-list-list-atblp-of-clause.aux-limsplit
   (implies (force (and (logic.term-listp todo)
                        (logic.term-list-atblp todo atbl)
                        (logic.term-list-atblp done atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (true-listp todo)))
            (equal (logic.term-list-list-atblp (clause.aux-limsplit todo done n) atbl)
                   t)))

 (verify-guards clause.aux-limsplit)

 (defthm forcing-cons-listp-of-clause.aux-limsplit
   (implies (force (and (or (consp todo)
                            (consp done))
                        (true-listp todo)))
            (equal (cons-listp (clause.aux-limsplit todo done n))
                   t))))





;; (defthmd clause.aux-limsplit-when-double-negative
;;   (implies (and (not (zp n))
;;                 (clause.negative-termp a)
;;                 (clause.negative-termp (clause.negative-term-guts a)))
;;            (equal (clause.aux-limsplit (cons a x) done n)
;;                   (clause.aux-limsplit (cons (clause.negative-term-guts (clause.negative-term-guts a)) x) done n)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-limsplit))))

;; (defthmd clause.aux-limsplit-when-negative-1
;;   (implies (and (not (zp n))
;;                 (clause.negative-termp a)
;;                 (not (clause.negative-termp (clause.negative-term-guts a)))
;;                 (not (logic.functionp (clause.negative-term-guts a))))
;;            (equal (clause.aux-limsplit (cons a x) done n)
;;                   (clause.aux-limsplit x (cons (logic.function 'not (list (clause.negative-term-guts a))) done) n)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-limsplit))))

;; (defthmd clause.aux-limsplit-when-negative-2
;;   (implies (and (not (zp n))
;;                 (clause.negative-termp a)
;;                 (not (clause.negative-termp (clause.negative-term-guts a)))
;;                 (not (equal (logic.function-name (clause.negative-term-guts a)) 'if)))
;;            (equal (clause.aux-limsplit (cons a x) done n)
;;                   (clause.aux-limsplit x (cons (logic.function 'not (list (clause.negative-term-guts a))) done) n)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-limsplit))))

;; (defthmd clause.aux-limsplit-when-negative-3
;;   (implies (and (not (zp n))
;;                 (clause.negative-termp a)
;;                 (not (clause.negative-termp (clause.negative-term-guts a)))
;;                 (not (equal (len (logic.function-args (clause.negative-term-guts a))) 3)))
;;            (equal (clause.aux-limsplit (cons a x) done n)
;;                   (clause.aux-limsplit x (cons (logic.function 'not (list (clause.negative-term-guts a))) done) n)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-limsplit))))

;; (defthmd clause.aux-limsplit-when-negative-4
;;   (implies (and (not (zp n))
;;                 (clause.negative-termp a)
;;                 (not (clause.negative-termp (clause.negative-term-guts a)))
;;                 (logic.functionp (clause.negative-term-guts a))
;;                 (equal (logic.function-name (clause.negative-term-guts a)) 'if)
;;                 (equal (len (logic.function-args (clause.negative-term-guts a))) 3)
;;                 (force (true-listp x)))
;;            (equal (clause.aux-limsplit (cons a x) done n)
;;                   (revappend (clause.aux-limsplit (cons (logic.function 'not (list (first (logic.function-args (clause.negative-term-guts a)))))
;;                                                         (cons (logic.function 'not (list (second (logic.function-args (clause.negative-term-guts a)))))
;;                                                               x))
;;                                                   done
;;                                                   (- n 1))
;;                              (clause.aux-limsplit (cons (first (logic.function-args (clause.negative-term-guts a)))
;;                                                         (cons (logic.function 'not (list (third (logic.function-args (clause.negative-term-guts a)))))
;;                                                               x))
;;                                                   done
;;                                                   (- n 1)))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-limsplit))))

;; (defthmd clause.aux-limsplit-when-positive-1
;;   (implies (and (not (zp n))
;;                 (not (clause.negative-termp a))
;;                 (not (logic.functionp a)))
;;            (equal (clause.aux-limsplit (cons a x) done n)
;;                   (clause.aux-limsplit x (cons a done) n)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-limsplit))))

;; (defthmd clause.aux-limsplit-when-positive-2
;;   (implies (and (not (zp n))
;;                 (not (clause.negative-termp a))
;;                 (not (equal (logic.function-name a) 'if)))
;;            (equal (clause.aux-limsplit (cons a x) done n)
;;                   (clause.aux-limsplit x (cons a done) n)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-limsplit))))

;; (defthmd clause.aux-limsplit-when-positive-3
;;   (implies (and (not (zp n))
;;                 (not (clause.negative-termp a))
;;                 (not (equal (len (logic.function-args a)) 3)))
;;            (equal (clause.aux-limsplit (cons a x) done n)
;;                   (clause.aux-limsplit x (cons a done) n)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-limsplit))))

;; (defthmd clause.aux-limsplit-when-positive-4
;;   (implies (and (not (zp n))
;;                 (not (clause.negative-termp a))
;;                 (logic.functionp a)
;;                 (equal (logic.function-name a) 'if)
;;                 (equal (len (logic.function-args a)) 3)
;;                 (force (true-listp x)))
;;            (equal (clause.aux-limsplit (cons a x) done n)
;;                   (revappend (clause.aux-limsplit (cons (logic.function 'not (list (first (logic.function-args a))))
;;                                                         (cons (second (logic.function-args a))
;;                                                               x))
;;                                                   done
;;                                                   (- n 1))
;;                              (clause.aux-limsplit (cons (first (logic.function-args a))
;;                                                         (cons (third (logic.function-args a))
;;                                                               x))
;;                                                   done
;;                                                   (- n 1)))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-limsplit))))

;; (defthmd clause.aux-limsplit-when-not-consp
;;   (implies (and (not (zp n))
;;                 (not (consp todo))
;;                 (force (true-listp todo)))
;;            (equal (clause.aux-limsplit todo done n)
;;                   (list done)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-limsplit))))

;; (defthmd clause.aux-limsplit-when-zp
;;   (implies (and (zp n)
;;                 (force (true-listp todo)))
;;            (equal (clause.aux-limsplit todo done n)
;;                   (list (revappend done todo))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-limsplit))))

;; (deftheory clause.aux-limsplit-openers
;;   '(clause.aux-limsplit-when-double-negative
;;     clause.aux-limsplit-when-negative-1
;;     clause.aux-limsplit-when-negative-1
;;     clause.aux-limsplit-when-negative-2
;;     clause.aux-limsplit-when-negative-3
;;     clause.aux-limsplit-when-negative-4
;;     clause.aux-limsplit-when-positive-1
;;     clause.aux-limsplit-when-positive-2
;;     clause.aux-limsplit-when-positive-3
;;     clause.aux-limsplit-when-positive-4
;;     clause.aux-limsplit-when-not-consp
;;     clause.aux-limsplit-when-zp))





(definlined clause.simple-limsplit (clause n)
  (declare (xargs :guard (and (logic.term-listp clause)
                              (true-listp clause)
                              (consp clause)
                              (natp n))))
  (clause.aux-limsplit clause nil n))

(defthm true-listp-of-clause.simple-limsplit
  (implies (force (true-listp clause))
           (equal (true-listp (clause.simple-limsplit clause n))
                  t))
  :hints(("Goal" :in-theory (enable clause.simple-limsplit))))

;; (defthm consp-of-clause.simple-limsplit
;;   (implies (force (true-listp clause))
;;            (equal (consp (clause.simple-limsplit clause n))
;;                   t))
;;   :hints(("Goal" :in-theory (enable clause.simple-limsplit))))

;; (defthm clause.simple-limsplit-under-iff
;;   (implies (force (true-listp clause))
;;            (iff (clause.simple-limsplit clause n)
;;                 t))
;;   :hints(("Goal" :in-theory (enable clause.simple-limsplit))))

(defthm forcing-term-list-listp-of-clause.simple-limsplit
  (implies (force (and (logic.term-listp clause)
                       (true-listp clause)))
           (equal (logic.term-list-listp (clause.simple-limsplit clause n))
                  t))
  :hints(("Goal" :in-theory (enable clause.simple-limsplit))))

(defthm forcing-term-list-list-atblp-of-clause.simple-limsplit
  (implies (force (and (logic.term-listp clause)
                       (true-listp clause)
                       (logic.term-list-atblp clause atbl)
                       (equal (cdr (lookup 'not atbl)) 1)))
           (equal (logic.term-list-list-atblp (clause.simple-limsplit clause n) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.simple-limsplit))))

(defthm forcing-cons-listp-of-clause.simple-limsplit
  (implies (force (and (consp clause)
                       (true-listp clause)))
           (equal (cons-listp (clause.simple-limsplit clause n))
                  t))
  :hints(("Goal" :in-theory (enable clause.simple-limsplit))))
