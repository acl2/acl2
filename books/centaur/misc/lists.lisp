; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")


;; Supplementing list-defthms, moving to a slightly different approach.

;; - For functions like take, etc that could have convenient
;; cdr-recursive definitions but don't, we make new definition rules and
;; corresponding induction rules.

;; - We try to avoid natp hyps and instead use nfix in RHSes where necessary.
;; We prove nat-equiv congruences where appropriate (and not already done in arith-equivs).

;; - For functions like SUBSEQ and BUTLAST which should have reasonable
;; recursive definitions and congruences but don't, we'll rewrite them to
;; functions suffixed with X that do, under appropriate constraints.

;; (future):
;; - For rewrite rules that cause case splits, we prove separate rules for all
;; the cases and leave the splitting rule disabled by default.  We add these to
;; a ruleset to keep track.

;; - We prove list-equiv congruences where appropriate.

;; [Jared] moved most of the pure list-equiv stuff into std/lists/equiv.lisp

(include-book "std/basic/arith-equivs" :dir :system)
(include-book "std/lists/equiv" :dir :system)
(local (include-book "std/lists/take" :dir :system))
(include-book "data-structures/list-defthms" :dir :system)


(defun cdr-cdr-dec-ind (x y n)
  (declare (xargs :measure (+ (len x) (len y) (nfix n))
                  :hints(("Goal" :in-theory (enable nfix)))))
  (if (and (atom x) (atom y) (zp n))
      nil
    (cdr-cdr-dec-ind (cdr x) (cdr y) (1- (nfix n)))))



#||

(local (in-theory (enable* arith-equiv-forwarding)))
(local (include-book "arithmetic/top-with-meta" :dir :system))



(local (in-theory (enable list-fix)))


(defun cdr-cdr-ind (x y)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (and (atom x) (atom y))
      nil
    (cdr-cdr-ind (cdr x) (cdr y))))


;; ------------------- REVAPPEND -------------------------------
;; Supposing we let REVERSE open into revappend -- this means we don't need
;; (not (stringp x)) hyps.

(defthm revappend-to-append
  (implies (syntaxp (not (equal b ''nil)))
           (equal (revappend a b)
                  (append (revappend a nil) b))))

(in-theory (disable binary-append-revappend))

(theory-invariant (not (and (active-runep '(:rewrite revappend-to-append))
                            (active-runep '(:rewrite binary-append-revappend)))))


;; ------------------- TAKE redefinition --------------------------

(defthm take-rec
  (equal (take n x)
         (if (zp n)
             nil
           (cons (car x)
                 (take (1- n) (cdr x)))))
  :rule-classes ((:definition :controller-alist ((take t nil)))))

(defthm take-ind
  t
  :rule-classes ((:induction
                  :pattern (take n x)
                  :scheme (xfirstn n x))))

(in-theory (disable take-is-xfirstn take))

;; ------------------- SUBSEQ-LIST redefinition --------------------------

(defun subseqx (lst start end)
  (declare (xargs :guard (and (true-listp lst)
                              (natp start)
                              (integerp end)
                              (<= start end)
                              (<= end (length lst)))
                  :verify-guards nil))
  (mbe :logic (if (zp start)
                  (take end lst)
                (subseqx (cdr lst) (1- start) (1- (nfix end))))
       :exec (subseq lst start end)))

(defthm subseq-list-is-subseqx
  (implies (and (natp start)
                (integerp end)
                (<= start end))
           (equal (subseq-list lst start end)
                  (subseqx lst start end)))
  :hints (("goal" :induct (subseqx lst start end))))

(verify-guards subseqx)

(defun cdr-cdr-dec-dec-ind (x y n m)
  (declare (xargs :measure (+ (len x) (len y) (nfix n) (nfix m))
                  :hints(("Goal" :in-theory (enable nfix)))))
  (if (and (atom x) (atom y) (zp n) (zp m))
      nil
    (cdr-cdr-dec-dec-ind (cdr x) (cdr y) (1- (nfix n)) (1- (nfix m)))))

(defcong list-equiv equal (subseqx lst start end) 1
  :hints (("goal" :induct (cdr-cdr-dec-dec-ind lst lst-equiv start end)
           :expand ((:free (lst) (subseqx lst start end)))
           :in-theory (disable list-equiv))))

(defcong nat-equiv equal (subseqx list start end) 2)
(defcong nat-equiv equal (subseqx list start end) 3)

;; ------------------- BUTLAST redefinition --------------------------

(defun butlastx (lst n)
  (declare (xargs :guard (and (true-listp lst)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (if (<= (len lst) (nfix n))
                  nil
                (cons (car lst)
                      (butlastx (cdr lst) n)))
       :exec (butlast lst n)))

(defthm butlast-is-butlastx
  (implies (natp n)
           (equal (butlast lst n)
                  (butlastx lst n)))
  :hints(("Goal" :in-theory (enable butlast)
          :induct (butlastx lst n))))

(verify-guards butlastx)

(defcong list-equiv equal (butlastx lst n) 1
  :hints(("Goal" :in-theory (disable list-equiv)
          :induct (cdr-cdr-ind lst lst-equiv))))

(defcong nat-equiv equal (butlastx lst n) 2)


;; ------------------- MAKE-LIST-AC redefinition --------------------------

;; Note: this is now make-list-ac-redef in list-defthms.lisp
;; (defthm make-list-ac-rec
;;   (equal (make-list-ac n val ac)
;;          (if (zp n)
;;              ac
;;            (cons val (make-list-ac (1- n) val ac))))
;;   :rule-classes ((:definition :controller-alist ((make-list-ac t nil nil)))))

;; (defun make-list-ac-rec-ind (n val ac)
;;   (if (zp n)
;;       (list val ac)
;;     (make-list-ac-rec-ind (1- n) val ac)))

;; (defthm make-list-ac-induct
;;   t
;;   :rule-classes ((:induction
;;                   :pattern (make-list-ac n val ac)
;;                   :scheme (make-list-ac-rec-ind n val ac))))

(defcong nat-equiv equal (make-list-ac n val ac) 1)

||#

