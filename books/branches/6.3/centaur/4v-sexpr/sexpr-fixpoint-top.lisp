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

(include-book "sexpr-fixpoint")

(include-book "sexpr-equivs")

(local (include-book "sexpr-fixpoint-correct"))

(set-enforce-redundancy t)

(defquant 4v-sexpr-fixpointp (ups vals)
  (forall k (implies (hons-assoc-equal k ups)
                     (4v-sexpr-equiv (4v-sexpr-restrict
                                      (cdr (hons-assoc-equal k ups))
                                      vals)
                                     (cdr (hons-assoc-equal k vals))))))


(defquant 4v-sexpr-fixpoint-lower-boundp (ups lb)
  (forall (fp env)
          (implies (and (keys-equiv ups fp)
                        (4v-alist-<= (4v-sexpr-eval-alist ups (make-fal fp env))
                                     fp))
                   (4v-alist-<= (4v-sexpr-eval-alist lb env) fp))))



(defthm 4v-sexpr-fixpointp-sexpr-fixpoints
  (4v-sexpr-fixpointp ups (sexpr-fixpoints ups)))



(defthm 4v-sexpr-fixpoint-lower-boundp-sexpr-fixpoints
  (4v-sexpr-fixpoint-lower-boundp ups (sexpr-fixpoints ups)))


(defthm keys-of-sexpr-fixpoints
  (iff (hons-assoc-equal x (sexpr-fixpoints update-fns))
       (hons-assoc-equal x update-fns)))


(defthm fixpoint-vars-are-vars-of-update-fns
  (implies (not (member-equal x (4v-sexpr-vars-list (alist-vals update-fns))))
           (not (member-equal x (4v-sexpr-vars-list
                                 (alist-vals (sexpr-fixpoints update-fns)))))))

(defthm keys-not-present-in-fixpoint-vars
  (implies (member-equal x (alist-keys update-fns))
           (not (member-equal
                 x (4v-sexpr-vars-list
                    (alist-vals (sexpr-fixpoints update-fns)))))))



(defthm 4v-sexpr-least-fixpoint-unique
  (implies (and (4v-sexpr-fixpoint-lower-boundp update-fns lb1)
                (4v-sexpr-fixpoint-lower-boundp update-fns lb2)
                (4v-sexpr-fixpointp update-fns lb1)
                (4v-sexpr-fixpointp update-fns lb2)
                (keys-equiv lb1 update-fns)
                (keys-equiv lb2 update-fns))
           (4v-sexpr-alist-equiv lb1 lb2))
  :rule-classes nil)







(defthm sexpr-fixpoint-with-varmap-least-fixpointp
  (and (4v-sexpr-fixpointp ups (sexpr-fixpoint-with-varmap ups map))
       (4v-sexpr-fixpoint-lower-boundp
        ups (sexpr-fixpoint-with-varmap ups map))))

(defthm keys-sexpr-fixpoint-with-varmap
  (iff (hons-assoc-equal x (sexpr-fixpoint-with-varmap ups map))
       (hons-assoc-equal x ups)))

(defthm vars-sexpr-fixpoint-with-varmap-when-not-used
  (implies (not (member-equal x (4v-sexpr-vars-list (alist-vals ups))))
           (not (member-equal x (4v-sexpr-vars-list
                                 (alist-vals (sexpr-fixpoint-with-varmap
                                              ups map)))))))

(defthm vars-sexpr-fixpoint-with-varmap-when-bound
  (implies (member-equal x (alist-keys ups))
           (not (member-equal x (4v-sexpr-vars-list (alist-vals
                                                  (sexpr-fixpoint-with-varmap
                                                   ups map)))))))


(in-theory (disable sexpr-fixpoint-with-varmap
                    sexpr-fixpoints))



(defcong 4v-sexpr-alist-equiv iff (4v-sexpr-fixpoint-lower-boundp ups lb) 1)
(defcong 4v-sexpr-alist-equiv iff (4v-sexpr-fixpoint-lower-boundp ups lb) 2)

(defcong 4v-sexpr-alist-equiv iff (4v-sexpr-fixpointp ups fixpoint) 1)
(defcong 4v-sexpr-alist-equiv iff (4v-sexpr-fixpointp ups fixpoint) 2)

(defcong 4v-sexpr-alist-equiv 4v-sexpr-alist-equiv (sexpr-fixpoints ups) 1)


