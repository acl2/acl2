; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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


