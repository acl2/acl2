
; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

; "nary" congruences for loghead

(in-package "ACL2")
(include-book "tools/rulesets" :dir :system)
(include-book "coi/nary/nary" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "ihs-extensions"))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; allow LOGHEAD to be used as an Nary defcong+ context
(acl2::defcontext (loghead n x) 2)

;; This is the same as nary's defcong+, except that it doesn't wrap a
;; skip-rewrite around the conclusion.  Subjectively I think this seems to work
;; better, but perhaps there are pitfalls.
(defmacro defcong+-
  (name term &key (hyps 'nil) (cong 'nil) (check 'nil) (hints 'nil) (equiv 'equal))
  (declare (type (satisfies wf-cong-list) cong))

  `(defthm ,name
     (implies
      (and

       ;; This is supposed to help stop us from calling ourselves
       ;; recursively on the rewritten RHS of this theorem.  When it works, it
       ;; reduces the cost of this rule from quardratic to linear.
       ;; Unfortunately, it only works when :Brr is enabled.  Help!

       ;; (bind-free (non-recursive ',name mfc state) (ok))

       ;; Check the hyps

       ,@(if hyps `(,hyps) nil)

       ;; Simplify selected arguments in their new context

       ,@(generate-cong-hyps nil cong)

       ;; See if anything has changed ..

       ,(generate-cong-syntax-hyps cong)

       ;; Check the types of our results

       ,@(if check `(,check) nil))
      (,equiv ,term
              ,(replace-cong-terms cong term)))
     ,@(if hints `(:hints ,hints) nil)
     ;;`(:hints (("Goal" :in-theory (enable ,@(cong-equivs cong)))))))
     ))




(local
 (encapsulate
   nil
   (local (defun ind (n m a b c)
            (if (zp n)
                (list m a b c)
              (ind (1- n) (1- m)
                   (logcdr a)
                   (logcdr b)
                   (b-ior (b-and (logcar a) (logcar b))
                          (b-ior
                           (b-and (logcar a) (logcar c))
                           (b-and (logcar b) (logcar c))))))))

   (defthm loghead-of-sum-lemma
     (implies (and (integerp a)
                   (integerp b)
                   (bitp c)
                   (<= (nfix n) (nfix m)))
              (equal (loghead n (+ c a (loghead m b)))
                     (loghead n (+ c a b))))
     :hints (("goal"
              :induct (ind n m a b c)
              :do-not '(generalize fertilize)
              :expand ((:free (b) (loghead n b))
                       (:free (b) (loghead m b)))
              :in-theory (e/d (nfix logcdr-of-bit b-and b-ior)
                              (loghead-identity))
              :do-not-induct t))
     :rule-classes nil)))

(defthmd loghead-of-minus-of-loghead
  (implies (and (integerp b)
                (<= (nfix n) (nfix m)))
           (equal (loghead n (- (loghead m b)))
                  (loghead n (- b))))
  :hints (("goal" :in-theory (e/d (minus-to-lognot))
           :use ((:instance loghead-of-sum-lemma
                  (c 1) (a 0) (b (lognot (loghead m b))))
                 (:instance loghead-of-sum-lemma
                  (c 1) (a 0) (b (lognot b)))))))

(defthmd loghead-of-plus-loghead-first
  (implies (and (integerp a)
                (integerp b)
                (<= (nfix n) (nfix m)))
           (equal (loghead n (+ (loghead m b) a))
                  (loghead n (+ a b))))
  :hints (("goal" :use ((:instance loghead-of-sum-lemma (c 0))))))

(defthmd loghead-of-plus-loghead-second
  (implies (and (integerp a)
                (integerp b)
                (<= (nfix n) (nfix m)))
           (equal (loghead n (+ a (loghead m b)))
                  (loghead n (+ a b))))
  :hints (("goal" :use ((:instance loghead-of-sum-lemma (c 0))))))

(defcong+-
  loghead-of-plus-cong
  (loghead n (+ a b))
  :hyps (and (integerp a)
             (integerp b))
  :cong ((a (equal x (loghead n a)))
         (b (equal y (loghead n b))))
  :check (and (integerp x) (integerp y))
  :hints(("Goal" :use ((:instance LOGHEAD-OF-PLUS-LOGHEAD-FIRST
                        (m n) (n n) (a a) (b b))
                       (:instance LOGHEAD-OF-PLUS-LOGHEAD-FIRST
                        (m n) (n n) (a a) (b y))
                       (:instance LOGHEAD-OF-PLUS-LOGHEAD-FIRST
                        (m n) (n n) (a y) (b x))
                       (:instance LOGHEAD-OF-PLUS-LOGHEAD-FIRST
                        (m n) (n n) (a y) (b a))))))


(defcong+-
  loghead-of-logtail-cong
  (loghead n (logtail m a))
  :hyps (equal nn (+ (nfix n) (nfix m)))
  :cong ((a (equal x (loghead nn a))))
  :hints (("goal" :use ((:instance logtail-of-loghead
                         (n m) (m (+ (nfix m) (nfix n)))
                         (x a))
                        (:instance logtail-of-loghead
                         (n m) (m (+ (nfix m) (nfix n)))
                         (x x)))
           :in-theory (disable logtail-of-loghead))))


(defcong+-
  loghead-of-ash-cong
  (loghead n (ash a m))
  :hyps (equal nn (- (nfix n) (ifix m)))
  :cong ((a (equal x (loghead nn a))))
  :hints(("Goal" :in-theory (enable loghead-of-ash nfix ifix ash-0
                                    loghead**))))

(defcong+-
  loghead-of-minus-cong
  (loghead n (- a))
  :hyps (integerp a)
  :cong ((a (equal x (loghead n a))))
  :check (integerp x)
  :hints(("Goal" :use ((:instance loghead-of-minus-of-loghead
                        (m n) (n n) (b x))
                       (:instance loghead-of-minus-of-loghead
                        (m n) (n n) (b a))))))

(defcong+-
  loghead-of-logior-cong
  (loghead n (logior a b))
  :cong ((a (equal x (loghead n a)))
         (b (equal y (loghead n b)))))

(defcong+-
  logbitp-to-loghead-cong
  (logbitp n x)
  :hyps (equal nn (+ 1 (nfix n)))
  :cong ((x (equal a (loghead nn x))))
  :hints (("goal" :use ((:instance logbitp-of-loghead-split
                         (i x) (pos n) (size (+ 1 (nfix n))))
                        (:instance logbitp-of-loghead-split
                         (i a) (pos n) (size (+ 1 (nfix n)))))
           :in-theory (disable logbitp-of-loghead-split
                               logbitp-of-loghead-in-bounds
                               (force)))))

(def-ruleset! loghead-cong-rules
  '(loghead-of-logior-cong
    loghead-of-minus-cong
    loghead-of-ash-cong
    logbitp-to-loghead-cong
    loghead-of-plus-cong))

(in-theory (disable* loghead-cong-rules))
