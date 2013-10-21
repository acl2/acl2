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

(in-package "ACL2")

; Sigh.  This is exactly the same as the varmap book under ../aig, but it
; doesn't require that NIL not be a member of the keys.
;
; [Jared] After consideration, we think this is the right book to use; the FAIG
; monotonicity stuff was just too hard and should eventually be scrapped.

(include-book "centaur/aig/base" :dir :system)
(include-book "centaur/misc/fast-alists" :dir :system)
(include-book "centaur/misc/hons-sets" :dir :system)
(local (include-book "data-structures/no-duplicates" :dir :system))


(defun svar-assoc (svar svarmap)
  (if (atom svarmap)
      nil
    (or (and (consp (car svarmap))
             (cond ((equal svar (cadar svarmap))
                    (cons (caar svarmap) t))
                   ((equal svar (cddar svarmap))
                    (cons (caar svarmap) nil))))
        (svar-assoc svar (cdr svarmap)))))

(defthm svar-assoc-implies-hons-assoc-equal
  (implies (svar-assoc svar svarmap)
           (hons-assoc-equal (car (svar-assoc svar svarmap))
                             svarmap)))

(defun-sk good-svarmap-sigs (svarmap)
  (forall
   sig
   (let ((look (hons-assoc-equal sig svarmap)))
     (implies look
              (and (equal (svar-assoc (cadr look) svarmap)
                          (cons sig t))
                   (equal (svar-assoc (cddr look) svarmap)
                          (cons sig nil)))))))

(defun aig-svar-cons-val-alistp (x)
  (declare (Xargs :guard t))
  (or (atom x)
      (and (consp (car x))
           (consp (cdar x))
           (atom (cadar x))
           (not (booleanp (cadar x)))
           (atom (cddar x))
           (not (booleanp (cddar x)))
           (aig-svar-cons-val-alistp (cdr x)))))

(defun svarmap-vals (svarmap)
  (declare (Xargs :guard (aig-svar-cons-val-alistp svarmap)))
  (if (atom svarmap)
      nil
    (if (atom (car svarmap))
        (svarmap-vals (cdr svarmap))
      (list* (cadar svarmap) (cddar svarmap)
             (svarmap-vals (cdr svarmap))))))

(defthm member-svarmap-vals-impl-svar-assoc
  (implies (member-equal x (svarmap-vals svarmap))
           (svar-assoc x svarmap)))

(defthm not-member-svarmap-vals-impl-not-svar-assoc
  (implies (not (member-equal x (svarmap-vals svarmap)))
           (not (svar-assoc x svarmap))))

(defthm svar-assoc-when-no-duplicate-vals
  (let ((look (hons-assoc-equal sig svarmap)))
  (implies (and (no-duplicatesp-equal (svarmap-vals svarmap))
                look)
           (and (equal (svar-assoc (cadr look) svarmap)
                       (cons sig t))
                (equal (svar-assoc (cddr look) svarmap)
                       (cons sig nil)))))
  :hints (("goal" :induct (len svarmap))))

(defthm no-duplicate-vals-implies-good-svarmap-sigs
  (implies (no-duplicatesp-equal (svarmap-vals svarmap))
           (good-svarmap-sigs svarmap))
  :hints (("goal" :in-theory (enable good-svarmap-sigs)
           :do-not-induct t)))


(defun-sk good-svarmap-svars (svarmap)
  (forall
   svar
   (let ((key (svar-assoc svar svarmap)))
     (implies key
              (if (cdr key)
                  (equal (cadr (hons-assoc-equal (car key) svarmap))
                         svar)
                (equal (cddr (hons-assoc-equal (car key) svarmap))
                       svar))))))

(defthm no-duplicate-keys-impl-good-svarmap-svars1
  (let ((key (svar-assoc svar svarmap)))
    (implies (and (no-duplicatesp-equal (alist-keys svarmap))
                  key)
             (if (cdr key)
                 (equal (cadr (hons-assoc-equal (car key) svarmap))
                        svar)
               (equal (cddr (hons-assoc-equal (car key) svarmap))
                      svar))))
  :hints(("Goal" :in-theory (enable alist-keys)))
  :rule-classes nil)

(defthm no-duplicate-keys-impl-good-svarmap-svars
  (implies (no-duplicatesp-equal (alist-keys svarmap))
           (good-svarmap-svars svarmap))
  :hints(("Goal" :use ((:instance
                        no-duplicate-keys-impl-good-svarmap-svars1
                        (svar (good-svarmap-svars-witness svarmap))))
          :in-theory (enable good-svarmap-svars)
          :do-not-induct t)))

(defun good-svarmap (svarmap)
  (declare (Xargs :guard t))
  (and (aig-svar-cons-val-alistp svarmap)
       (let ((keys (alist-keys svarmap))
             (vals (svarmap-vals svarmap)))
         (and (not (hons-dups-p keys))
              (not (hons-dups-p vals))
              ;; (not (member-equal nil keys))
              (not (member-equal nil vals))))))

(in-theory (disable good-svarmap-svars
                    good-svarmap-sigs
                    good-svarmap-svars-necc
                    good-svarmap-sigs-necc
                    good-svarmap))

(defthm good-svarmap-impl-svars
  (let* ((key (svar-assoc svar svarmap))
         (svars (cdr (hons-assoc-equal (car key) svarmap))))
    (implies
     (and (good-svarmap svarmap)
          key)
     (and (implies (cdr key)
                   (equal (car svars) svar))
          (implies (not (cdr key))
                   (equal (cdr svars) svar)))))
  :hints(("Goal" :in-theory (e/d (good-svarmap))
          :use good-svarmap-svars-necc
          :do-not-induct t)))

(defthm good-svarmap-impl-sigs
  (implies (and (good-svarmap svarmap)
                (hons-assoc-equal sig svarmap))
           (and (equal (svar-assoc
                        (cadr (hons-assoc-equal sig svarmap))
                        svarmap)
                       (cons sig t))
                (equal (svar-assoc
                        (cddr (hons-assoc-equal sig svarmap))
                        svarmap)
                       (cons sig nil))))
  :hints(("Goal" :in-theory (e/d (good-svarmap))
          :use good-svarmap-sigs-necc
          :do-not-induct t)))


(defun sig-al-to-svar-al1 (al svarmap)
  (declare (xargs :guard (aig-svar-cons-val-alistp svarmap)))
  (if (atom al)
      nil
    (b* ((rest (sig-al-to-svar-al1 (cdr al) svarmap))
         ((when (atom (car al))) rest)
         (look (hons-get (caar al) svarmap))
         ((when (not look)) rest)
         (svars (cdr look))
         (vals (faig-fix (cdar al))))
      (hons-acons (car svars) (car vals)
                  (hons-acons (cdr svars) (cdr vals)
                              rest)))))

(memoize 'sig-al-to-svar-al1)

(defthm svar-assoc-key
  (implies (and (equal x (car (svar-assoc svar svarmap)))
                (svar-assoc svar svarmap))
           (hons-assoc-equal x svarmap))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil))))


(defthm lookup-in-sig-al-to-svar-al1
  (implies (and (good-svarmap svarmap)
                ;; (subsetp-equal (alist-keys al) (alist-keys svarmap))
                )
           (equal (hons-assoc-equal svar (sig-al-to-svar-al1 al svarmap))
                  (let* ((key (svar-assoc svar svarmap))
                         (look (hons-assoc-equal (car key) al)))
                    (and key look
                         (cons svar (if (cdr key)
                                       (car (faig-fix (cdr look)))
                                     (cdr (faig-fix (cdr look)))))))))
  :hints (("goal" :induct t
           :in-theory (e/d (alist-keys-member-hons-assoc-equal
                            alist-keys subsetp-equal)
                           (not-member-svarmap-vals-impl-not-svar-assoc
                            member-svarmap-vals-impl-svar-assoc
                            faig-fix default-car default-cdr)))))


(defthm sig-al-to-svar-al1-fake-cong
  (implies (and (good-svarmap svarmap)
                (alist-equiv env1 env2))
           (alist-equiv (sig-al-to-svar-al1 env1 svarmap)
                        (sig-al-to-svar-al1 env2 svarmap)))
  :hints (("goal" :use
           ((:instance alist-equiv-when-agree-on-bad-guy
                       (al1 (sig-al-to-svar-al1 env1 svarmap))
                       (al2 (sig-al-to-svar-al1 env2 svarmap))))
           :do-not-induct t)))



(defun svarmap-fix (svarmap)
  (declare (xargs :guard t))
  (if (good-svarmap svarmap)
      svarmap
    nil))

(defthm svarmap-fix-when-good-svarmap
  (implies (good-svarmap svarmap)
           (equal (Svarmap-fix svarmap) svarmap)))

(defthm good-svarmap-svarmap-fix
  (good-svarmap (svarmap-fix svarmap)))

(defthm good-svarmap-impl-aig-svar-cons-val-alistp
  (implies (good-svarmap x)
           (aig-svar-cons-val-alistp x))
  :hints(("Goal" :in-theory (enable good-svarmap))))

(defun sig-al-to-svar-al (al svarmap)
  (declare (xargs :guard (good-svarmap svarmap)))
  (sig-al-to-svar-al1 al (mbe :logic (svarmap-fix svarmap) :exec svarmap)))

(defcong alist-equiv alist-equiv (sig-al-to-svar-al env svarmap) 1
  :hints (("goal" :use ((:instance sig-al-to-svar-al1-fake-cong
                                   (env1 env) (env2 env-equiv)
                                   (svarmap (svarmap-fix svarmap))))
           :in-theory (disable sig-al-to-svar-al1-fake-cong
                               svarmap-fix))))

(defthm lookup-in-sig-al-to-svar-al
  (equal (hons-assoc-equal svar (sig-al-to-svar-al al svarmap))
         (let* ((key (svar-assoc svar (svarmap-fix svarmap)))
                (look (hons-assoc-equal (car key) al)))
           (and key look
                (cons svar (if (cdr key)
                              (car (faig-fix (cdr look)))
                            (cdr (faig-fix (cdr look))))))))
  :hints(("Goal" :in-theory (disable sig-al-to-svar-al1 svarmap-fix))))

(defthm sig-al-to-svar-al-svarmap-fix
  (equal (sig-al-to-svar-al al (svarmap-fix svarmap))
         (sig-al-to-svar-al al svarmap)))

(in-theory (disable sig-al-to-svar-al svarmap-fix))


(memoize 'sig-al-to-svar-al1)


(defthm good-svarmap-svar-assoc-nil
  (implies (good-svarmap svarmap)
           (not (svar-assoc nil svarmap)))
  :hints(("Goal" :in-theory (enable good-svarmap))))

;; (defthm good-svarmap-hons-assoc-equal-nil
;;   (implies (good-svarmap svarmap)
;;            (not (hons-assoc-equal nil svarmap)))
;;   :hints(("Goal" :in-theory (enable good-svarmap))))

(defthm good-svarmap-hons-assoc-equal-nil-sig-al-to-svar-al1
  (implies (good-svarmap svarmap)
           (not (hons-assoc-equal nil (sig-al-to-svar-al1 al svarmap)))))

(defthm hons-assoc-equal-nil-sig-al-to-svar-al
  (not (hons-assoc-equal nil (sig-al-to-svar-al al svarmap))))


(defthm true-listp-sig-al-to-svar-al1
  (true-listp (sig-al-to-svar-al1 al svarmap)))

(defthm true-listp-sig-al-to-svar-al
  (true-listp (sig-al-to-svar-al al svarmap))
  :hints(("Goal" :in-theory (enable sig-al-to-svar-al))))
