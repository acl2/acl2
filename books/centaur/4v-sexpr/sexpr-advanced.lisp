; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

; sexpr-advanced.lisp
;   - monotonicity results for sexpr eval, restrict, and compose

(in-package "ACL2")
(include-book "sexpr-vars")
(include-book "sexpr-equivs")
(set-inhibit-warnings "theory" "disable")


(defthm 4v-alist-<=-append1
  (implies (and (subsetp-equal (alist-keys b) (alist-keys a))
                (4v-alist-<= a b)
                (4v-alist-<= c d))
           (4v-alist-<= (append a c) (append b d)))
  :hints (("goal" :do-not-induct t :in-theory (disable 4v-fix))
          (witness :ruleset 4v-alist-<=-witnessing)
          (witness :ruleset 4v-alist-<=-hons-assoc-equal-example)
          (and stable-under-simplificationp
               '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                 (alist-keys-member-hons-assoc-equal 4v-fix))))
          (set-reasoning)))



(defthm 4v-sexpr-eval-monotonic
  (implies (and (4v-sexpr-<= a b)
                (4v-alist-<= c d))
           (4v-<= (4v-sexpr-eval a c)
                  (4v-sexpr-eval b d)))
  :hints(("Goal" :in-theory (e/d (4v-<=-trans1) (4v-<=)))
         (witness :ruleset 4v-sexpr-<=-example)))

(defthm 4v-sexpr-alist-<=-append
  (implies (and (4v-sexpr-alist-<= a b)
                (4v-sexpr-alist-<= c d)
                (set-equiv (alist-keys a) (alist-keys b)))
           (4v-sexpr-alist-<= (append a c) (append b d)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                           (4v-fix alist-keys-member-hons-assoc-equal)))
          (witness :ruleset (4v-sexpr-alist-<=-witnessing))
          (witness :ruleset (4v-sexpr-alist-<=-hons-assoc-equal-example))))

(defthm-4v-sexpr-flag
  (defthm 4v-sexpr-eval-when-agree-on-keys
    (implies (4v-alists-agree (4v-sexpr-vars x) a b)
             (equal (equal (4v-sexpr-eval x a)
                           (4v-sexpr-eval x b))
                    t))
    :flag sexpr)
  (defthm 4v-sexpr-eval-list-when-agree-on-keys
    (implies (4v-alists-agree (4v-sexpr-vars-list x) a b)
             (equal (equal (4v-sexpr-eval-list x a)
                           (4v-sexpr-eval-list x b))
                    t))
    :flag sexpr-list)
  :hints(("Goal" :in-theory (e/d (subsetp-equal)
                                 (4v-fix 4v-alists-agree-to-4v-env-equiv)))))

(defthm 4v-sexpr-eval-alist-when-agree-on-keys
  (implies (4v-alists-agree (4v-sexpr-vars-list (alist-vals x)) a b)
           (equal (equal (4v-sexpr-eval-alist x a)
                         (4v-sexpr-eval-alist x b))
                  t))
  :hints(("Goal" :in-theory
          (disable 4v-sexpr-eval
                   4v-alists-agree-to-4v-env-equiv))))



(defthm 4v-sexpr-restrict-monotonic
  (implies (and (4v-sexpr-<= a b)
                (4v-sexpr-alist-<= c d)
                (set-equiv (alist-keys c) (alist-keys d)))
           (4v-sexpr-<= (4v-sexpr-restrict a c)
                        (4v-sexpr-restrict b d)))
  :hints (("goal" :in-theory (disable 4v-fix 4v-<=)
           :do-not-induct t)
          (witness :ruleset (4v-sexpr-<=-witnessing))))

(defthm 4v-sexpr-restrict-alist-monotonic
  (implies (and (4v-sexpr-alist-<= a b)
                (4v-sexpr-alist-<= c d)
                (set-equiv (double-rewrite (alist-keys c))
                            (double-rewrite (alist-keys d))))
           (4v-sexpr-alist-<= (4v-sexpr-restrict-alist a c)
                              (4v-sexpr-restrict-alist b d)))
  :hints (("goal" :in-theory (disable 4v-fix 4v-<=)
           :do-not-induct t)
          (witness :ruleset 4v-sexpr-alist-<=-witnessing)
          (and stable-under-simplificationp
               '(:use ((:instance 4v-sexpr-restrict-monotonic
                                  (a (cdr (hons-get k0 a)))
                                  (b (cdr (hons-get k0 b)))))))
          (witness :ruleset 4v-sexpr-alist-<=-hons-assoc-equal-example)))



(defthm 4v-sexpr-compose-monotonic
  (implies (and (4v-sexpr-<= a b)
                (4v-sexpr-alist-<= c d)
                ;; (set-equiv (alist-keys c) (alist-keys d))
                )
           (4v-sexpr-<= (4v-sexpr-compose a c)
                        (4v-sexpr-compose b d)))
  :hints (("goal" :in-theory (disable 4v-fix 4v-<=)
           :do-not-induct t)
          (witness :ruleset (4v-sexpr-<=-witnessing))))

(defthm 4v-sexpr-compose-alist-monotonic
  (implies (and (4v-sexpr-alist-<= a b)
                (4v-sexpr-alist-<= c d)
                ;; (set-equiv (double-rewrite (alist-keys c))
                ;;             (double-rewrite (alist-keys d)))
                )
           (4v-sexpr-alist-<= (4v-sexpr-compose-alist a c)
                              (4v-sexpr-compose-alist b d)))
  :hints (("goal" :in-theory (disable 4v-fix 4v-<=)
           :do-not-induct t)
          (witness :ruleset 4v-sexpr-alist-<=-witnessing)
          (and stable-under-simplificationp
               '(:use ((:instance 4v-sexpr-compose-monotonic
                                  (a (cdr (hons-get k0 a)))
                                  (b (cdr (hons-get k0 b)))))))
          (witness :ruleset 4v-sexpr-alist-<=-hons-assoc-equal-example)))



(defsection bind-to-each
  (defun bind-to-each (keys val)
    (declare (xargs :guard t))
    (if (atom keys)
        nil
      (cons (cons (car keys) val)
            (bind-to-each (cdr keys) val))))

  (defthm lookup-in-bind-to-each
    (equal (hons-assoc-equal k (bind-to-each keys val))
           (and (member k keys)
                (cons k val)))))


(defsection 4v-al-to-sexpr-al
  (defun 4v-al-to-sexpr-al (al)
    (declare (xargs :guard t))
    (cond ((atom al) nil)
          ((atom (car al)) (4v-al-to-sexpr-al (cdr al)))
          (t (cons (cons (caar al) (hons (4v-fix (cdar al)) nil))
                   (4v-al-to-sexpr-al (cdr al))))))

  (defthm 4v-al-to-sexpr-al-lookup
    (equal (hons-assoc-equal x (4v-al-to-sexpr-al al))
           (and (hons-assoc-equal x al)
                (cons x (list (4v-fix (cdr (hons-assoc-equal x al)))))))
    :hints(("Goal" :in-theory (e/d (hons-assoc-equal) (4v-fix)))))

  (defthm 4v-sexpr-eval-of-list-4v-fix
    (equal (4v-sexpr-eval (list (4v-fix x)) env)
           (4v-fix x)))

  (local (in-theory (disable 4v-sexpr-eval 4v-fix)))

  (defthm 4v-sexpr-eval-alist-of-4v-al-to-sexpr-al
    (4v-env-equiv (4v-sexpr-eval-alist (4v-al-to-sexpr-al al) env)
                  al)
    :hints ((witness))))



