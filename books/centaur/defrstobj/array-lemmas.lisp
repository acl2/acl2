; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "RSTOBJ")

(deflabel start-of-array-lemmas)

; array-lemmas.lisp
;
; Supporting lemmas about the functions that deal with STOBJ arrays in the
; logic; viz. make-list-ac, nth, and update-nth.
;
; Note: this book should only be locally included!  (We are messing with the
; enabled/disabled status of widely used functions, and also adding rewrite
; rules about them that may not be appropriate for other users.)

(defthm len-of-make-list-ac
  (equal (len (make-list-ac n val acc))
         (+ (nfix n) (len acc))))

(defthm true-listp-make-list-ac
  (equal (true-listp (make-list-ac n val ac))
         (true-listp ac))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
                       (implies (true-listp ac)
                                (true-listp (make-list-ac n val ac))))))



(defthm acl2-count-of-nth-weak
  (<= (acl2-count (nth n x))
      (acl2-count x))
  :rule-classes ((:rewrite) (:linear)))

(defthm acl2-count-of-nth-strong
  (implies (consp x)
           (< (acl2-count (nth n x))
              (acl2-count x)))
  :rule-classes ((:rewrite) (:linear)))



(defthm true-listp-of-update-nth
  (equal (true-listp (update-nth n val arr))
         (or (<= (len arr) (nfix n))
             (true-listp arr)))
  :rule-classes ((:rewrite)
                 (:type-prescription
                  :corollary
                  (implies (true-listp arr)
                           (true-listp (update-nth n val arr))))))

(defthm update-nth-same
  (implies (equal (nfix i) (nfix j))
           (equal (update-nth j b (update-nth i a l))
                  (update-nth j b l))))

(defthm update-nth-diff
  (implies (not (equal (nfix n) (nfix m)))
           (equal (update-nth n val1 (update-nth m val2 x))
                  (update-nth m val2 (update-nth n val1 x)))))

(defthm update-nth-diff-gather-constants
  ;; This is a special alternative to update-nth-diff that is willing to
  ;; reorder keys/vals in the wrong order, as long as the result will be a
  ;; completely constant update to a constant record.
  ;;
  ;; This isn't really enough.  It won't do the job for nests of updates.  But
  ;; it is good enough to get through the "matt-example" in basic-tests.lisp.
  ;; Without the rule, we fail to prove to-leaves-bad-bad, because we put the
  ;; keys into the wrong order and don't get all the constants resolved.
  (implies (and (syntaxp (and (quotep x)
                              (quotep n)
                              (quotep val1)
                              (or (not (quotep m))
                                  (not (quotep val2)))))
                (not (equal (nfix n) (nfix m))))
           (equal (update-nth n val1 (update-nth m val2 x))
                  (update-nth m val2 (update-nth n val1 x))))
  :rule-classes ((:rewrite :loop-stopper nil)))

(defthm update-nth-of-nth
  (equal (update-nth n (nth n arr) arr)
         (if (< (nfix n) (len arr))
             arr
           (update-nth n nil arr))))

(defthm update-nth-of-nth-other
  (implies (not (equal (nfix n) (nfix m)))
           (equal (update-nth n (nth n arr) (update-nth m val arr))
                  (if (< (nfix n) (len arr))
                      (update-nth m val arr)
                    (update-nth n nil (update-nth m val arr))))))

(in-theory (disable update-nth
                    make-list-ac
                    ;; Also disable the executable counterpart of make-list-ac
                    ;; because otherwise, when we reason about stobj creators,
                    ;; we might end up trying to create lists that are millions
                    ;; or billions of entries long.
                    (:executable-counterpart make-list-ac)))

(defthm combine-plus
  (implies (and (syntaxp (quotep a))
                (syntaxp (quotep b)))
           (equal (+ a b c)
                  (+ (+ a b) c))))

(defthm simplify-equal-plus-constants
  (implies (and (syntaxp (quotep a))
                (syntaxp (quotep c)))
           (equal (equal (+ a b) c)
                  (and (acl2-numberp c)
                       (equal (fix b) (- c a))))))


;; Special rules for structural stobj equality proofs

(defthmd equal-of-cons-rewrite
  (equal (equal x (cons a b))
         (and (consp x)
              (equal a (car x))
              (equal b (cdr x)))))

(defthmd expand-nth
  (implies (syntaxp (quotep n))
           (equal (nth n l)
                  (IF (ENDP L)
                      NIL
                      (IF (ZP N)
                          (CAR L)
                          (NTH (- N 1) (CDR L))))))
  :hints(("Goal" :in-theory (enable nth))))

(defthmd equal-len-with-constant
  (implies (and (syntaxp (quotep n))
                ;; Goofy, the goal is to only expand variables and cdrs of variables,
                ;; not cars or nths of variables.  We don't want to expand something
                ;; like
                ;;   (equal (len (nth *offset* stobj)) 4096)
                ;; which with expand-NTH above might turn into
                ;;   (equal (len (car (cddddr stobj))) 4096) or similar
                (syntaxp (or (atom x)
                             (equal (car x) 'cdr))))
           (equal (equal (len x) n)
                  (if (equal n 0)
                      (atom x)
                    (and (natp n)
                         (consp x)
                         (equal (len (cdr x)) (- n 1))))))
  :hints(("Goal" :in-theory (enable len))))


(deftheory array-lemmas
  (set-difference-theories (current-theory :here)
                           (current-theory 'start-of-array-lemmas)))




