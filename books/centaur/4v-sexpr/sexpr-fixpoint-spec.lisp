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

; sexpr-fixpoint-spec.lisp
;

(in-package "ACL2")
(include-book "sexpr-fixpoint")
(include-book "sexpr-advanced")
(include-book "misc/bash" :dir :system)

(local (in-theory (disable set::double-containment
                           set::nonempty-means-set)))

(set-default-hints '('(:do-not-induct t)))

(local (in-theory (disable append-of-nil)))


;; BOZO probably move all of this stuff into libraries ---------------------

(defthm keys-equiv-cdr-when-not-consp-car
  (implies (not (consp (car a)))
           (keys-equiv (cdr a) a))
  :hints (("Goal" :in-theory (enable hons-assoc-equal))
          (witness))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthmd keys-equiv-iff-set-equiv-alist-keys
  ;; BOZO move to fast-alists book?
  (iff (keys-equiv env1 env2)
       (set-equiv (alist-keys env1) (alist-keys env2)))
  :hints(("goal" :in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                 (set-equiv
                                  alist-keys-member-hons-assoc-equal)))
         (witness)))


;; (defthm member-equal-remove
;;   (iff (member-equal j (remove k x))
;;        (and (not (equal j k))
;;             (member-equal j x)))
;;   :hints (("goal" :induct (len x))))

(encapsulate
  ()
  (local (defthmd lemma
           (iff (set-equiv a (cons b c))
                (and (member-equal b a)
                     (set-equiv (remove b a) (remove b c))))
           :hints ((set-reasoning))))

  (defthmd set-equiv-breakdown-cons
    (equal (set-equiv a (cons b c))
           (and (member-equal b a)
                (set-equiv (remove b a) (remove b c))))
    :hints(("Goal" :use ((:instance lemma))))))

(defthmd set-equiv-breakdown-cons2
  (equal (set-equiv (cons b c) a)
         (and (member-equal b a)
              (set-equiv (remove b a) (remove b c))))
  :hints(("Goal" :use ((:instance set-equiv-breakdown-cons)))))


(local
 (defthm remove-when-not-member
   (implies (not (member-equal k x))
            (equal (remove k x)
                   (append x nil)))
   :hints(("Goal" :induct t
           :in-theory (enable remove)))))



;;; Matt K. mod, 12/2018: I'm renaming remove-assoc, formerly just below, as
;;; remove-assoc-hons (not to conflict with hons-remove-assoc in
;;; std/alists/hons-remove-assoc.lisp), to avoid conflict with remove-assoc now
;;; built into ACl2.  I'm also replacing "remove-assoc" everywhere below by
;;; "remove-assoc-hons".
(defun remove-assoc-hons (key al)
  (declare (xargs :guard t))
  (if (atom al)
      nil
    (if (or (atom (car al))
            (hons-equal (caar al) key))
        (remove-assoc-hons key (cdr al))
      (cons (car al) (remove-assoc-hons key (cdr al))))))

(encapsulate nil
  (local (set-default-hints nil))
  (defthm lookup-in-remove-assoc-hons
    (equal (hons-assoc-equal k (remove-assoc-hons key al))
           (and (not (equal key k))
                (hons-assoc-equal k al)))))

(defthm alist-keys-remove-assoc-hons
  (equal (alist-keys (remove-assoc-hons k a))
         (remove k (alist-keys a)))
  :hints (("goal" :induct t)))

(defthm keys-equiv-cdr-remove-assoc-hons-car
  (implies (and (keys-equiv a b)
                (no-duplicatesp-equal (alist-keys a))
                (consp (car a)))
           (equal (keys-equiv (cdr a)
                              (remove-assoc-hons (caar a) b))
                  t))
  :hints (("goal" :in-theory (enable keys-equiv-iff-set-equiv-alist-keys
                                     alist-keys)
           :do-not-induct t)
          (set-reasoning))
  :otf-flg t)

(defthm alist-equiv-cons-append-remove
  (implies (hons-assoc-equal k a)
           (alist-equiv (cons (cons k (cdr (hons-assoc-equal k a)))
                              (append (remove-assoc-hons k a)
                                      b))
                        (append a b)))
  :hints(("Goal" :in-theory (enable alist-equiv-iff-agree-on-bad-guy))))


;; --------------- end of library stuff ----------------------------




(encapsulate ()
  (local
   (defthm hons-assoc-equal-caar
     (implies (and (keys-equiv x y)
                   (consp (car x)))
              (hons-assoc-equal (caar x) y))))

  (defthm 4v-env-equiv-remove-assoc-hons
    (implies (and (not (4v-env-equiv a (remove-assoc-hons k b)))
                  (not (hons-assoc-equal k a)))
             (not (4v-env-equiv (cons (cons k v) a)
                                b)))
    :hints (("goal" :do-not-induct t
             :in-theory (disable 4v-fix))
            (witness :ruleset 4v-env-equiv-witnessing)
            (witness :ruleset 4v-env-equiv-hons-assoc-equal-ex))
    :otf-flg t))

(defthm 4v-alist-<=-append
  (implies (and (keys-equiv a b)
                (4v-alist-<= a b)
                (4v-alist-<= c d))
           (4v-alist-<= (append a c)
                        (append b d)))
  :hints (("goal" :do-not-induct t
           :in-theory (disable 4v-fix))
          (witness)
          (witness :ruleset (4v-alist-<=-4v-hons-assoc-equal-example))))

(defthm 4v-sexpr-alist-<=-acons
  (implies (not (hons-assoc-equal k al1))
           (iff (4v-sexpr-alist-<= (cons (cons k v) al1) al2)
                (and (4v-sexpr-<= v (cdr (hons-assoc-equal k al2)))
                     (4v-sexpr-alist-<= al1 al2))))
  :hints (("Goal" :do-not-induct t)
          (witness :ruleset (4v-sexpr-alist-<=-hons-assoc-equal-example
                             4v-sexpr-alist-<=-witnessing))))

(defthm 4v-sexpr-<=-restrict
  (implies (and (4v-sexpr-alist-<= a b)
                (keys-equiv a b))
           (4v-sexpr-<= (4v-sexpr-restrict x a)
                        (4v-sexpr-restrict x b)))
  :hints(("Goal" :in-theory (e/d (keys-equiv-iff-set-equiv-alist-keys)
                                 (4v-alist-<= 4v-sexpr-restrict 4v-sexpr-eval
                                              4v-<=)))
         (witness)))

(defthm 4v-sexpr-<=-restrict-x
  (implies (4v-sexpr-<= a b)
           (4v-sexpr-<= (4v-sexpr-restrict a (list (cons k *4vx-sexpr*)))
                        b))
  :hints (("goal" :in-theory (e/d (4v-<=-trans2) (4v-<=)))
          (Witness) (witness)))

(defthm 4v-sexpr-restrict-4v-sexpr-restrict
  (4v-sexpr-equiv (4v-sexpr-restrict (4v-sexpr-restrict x al1) al2)
                  (4v-sexpr-restrict x (append (4v-sexpr-restrict-alist al1 al2)
                                            al2)))
  :hints (("goal" :do-not-induct t)
          (witness))
  :otf-flg t)





(defquant 4v-sexpr-fixpointp (ups vals)
  (forall k (implies (hons-assoc-equal k ups)
                     (4v-sexpr-equiv (4v-sexpr-restrict
                                      (cdr (hons-assoc-equal k ups))
                                      vals)
                                     (cdr (hons-assoc-equal k vals))))))

(verify-guards 4v-sexpr-fixpointp)

(defexample 4v-sexpr-fixpointp-lookup-example
  :pattern (4v-sexpr-restrict (cdr (hons-assoc-equal k updatefns)) env)
  :templates (k)
  :instance-rulename 4v-sexpr-fixpointp-instancing)


(encapsulate nil
  (local (witness-disable set-consp-witnessing))
  (defthm 4v-sexpr-fixpointp-cdr-updatefns
    (implies (and (4v-sexpr-fixpointp updatefns vals)
                  (no-duplicatesp-equal (alist-keys updatefns)))
             (4v-sexpr-fixpointp (cdr updatefns) vals))
    :hints (("goal" :in-theory (enable hons-assoc-equal alist-keys no-duplicatesp-equal))
            (witness))))

(defun 4v-sexpr-fixpoint-spec (ups)
  (if (atom ups)
      nil
    (b* ((rest (4v-sexpr-fixpoint-spec (cdr ups)))
         ((when (atom (car ups))) rest)
         (name (caar ups))
         (upfn (cdar ups))
         (composed-with-rest
          (4v-sexpr-restrict upfn rest))
         (fixpoint (4v-sexpr-restrict composed-with-rest
                                   `((,name x))))
         (rest-restrict (4v-sexpr-restrict-alist
                         rest `((,name . ,fixpoint)))))
      (acons name fixpoint rest-restrict))))


(defthm sexpr-fixpoint-spec-hons-assoc-equal-iff
  (iff (hons-assoc-equal x (4v-sexpr-fixpoint-spec ups))
       (hons-assoc-equal x ups))
  :hints (("goal" :induct t)))




(defthmd 4v-sexpr-equiv-fixpoint-eval
  (let ((ev-bottom (4v-sexpr-eval x (cons (cons name 'x) env))))
    (equal (4v-sexpr-eval x (cons (cons name ev-bottom) env))
           ev-bottom))
  :hints (("goal" :use ((:instance 4v-sexpr-eval-monotonicp
                                   (env (cons (cons name 'x) env))
                                   (env1 (cons (cons name (4v-sexpr-eval x (cons
                                                                            (cons name 'x)
                                                                            env)))
                                               env)))))))




(defexample 4v-sexpr-fixpointp-hons-assoc-equal-ex
  :pattern (hons-assoc-equal k ups)
  :templates (k)
  :instance-rulename 4v-sexpr-fixpointp-instancing)

(defcong 4v-sexpr-alist-equiv iff (4v-sexpr-fixpointp ups fixpoint) 2
  :hints ((witness :ruleset (4v-sexpr-fixpointp-witnessing
                             4v-sexpr-fixpointp-hons-assoc-equal-ex))))


(defthm atom-fixpoint
  (implies (not (consp ups))
           (4v-sexpr-fixpointp ups x))
  :hints ((witness :ruleset 4v-sexpr-fixpointp-witnessing)))

(defthm atom-car-fixpoint
  (implies (not (consp (car ups)))
           (iff (4v-sexpr-fixpointp (cdr ups) x)
                (4v-sexpr-fixpointp ups x)))
  :hints (("Goal" :in-theory (enable hons-assoc-equal))
          (witness :ruleset (4v-sexpr-fixpointp-witnessing
                             4v-sexpr-fixpointp-hons-assoc-equal-ex))))



(local (defthm switch-append
         (implies (not (hons-assoc-equal x al))
                  (alist-equiv (append al (list (cons x v)))
                               (cons (cons x v) al)))
         :hints (("goal" :in-theory (enable
                                     alist-equiv-iff-agree-on-bad-guy)))))

(local (defthm switch-append-cons
         (implies (not (hons-assoc-equal x al))
                  (alist-equiv (append al (cons (cons x v) al2))
                               (cons (cons x v) (append al al2))))
         :hints (("goal" :in-theory (enable alist-equiv-iff-agree-on-bad-guy)))))





(encapsulate
  nil
  (local (set-default-hints nil))
  (make-event
   (b* (((er res)
         (simplify-with-prover
          '(implies (not (hons-assoc-equal name env1))
                        (let* ((x (4v-sexpr-restrict x env1))
                               (ev-bottom (4v-sexpr-eval x (cons (cons name 'x) env))))
                          (equal (4v-sexpr-eval x (cons (cons name ev-bottom)
                                                        env))
                                 ev-bottom)))
          nil '4v-sexpr-equiv-fixpoint-eval-special state))
        (res (prettyify-clause-lst res t (w state))))
     (value
      `(defthm 4v-sexpr-equiv-fixpoint-eval-special
         ,(car res)
         :hints (("goal" :use ((:instance 4v-sexpr-equiv-fixpoint-eval
                                          (x (4v-sexpr-restrict x env1)))))))))))


(local (defthm fixpoint-eval-lookup
         (implies (and (4v-sexpr-fixpointp ups fixpoint)
                       (hons-assoc-equal k ups))
                  (4v-sexpr-equiv
                   (cdr (hons-assoc-equal k fixpoint))
                   (4v-sexpr-restrict (cdr (hons-assoc-equal k ups))
                                   fixpoint)))
         :hints ((witness :ruleset 4v-sexpr-fixpointp-hons-assoc-equal-ex))))

(defthm 4v-sexpr-fixpointp-4v-sexpr-fixpoint-spec
  (implies (no-duplicatesp-equal (alist-keys ups))
           (4v-sexpr-fixpointp ups (4v-sexpr-fixpoint-spec ups)))
  :hints (("goal" :induct (4v-sexpr-fixpoint-spec ups)
           :in-theory (e/d (no-duplicatesp-equal alist-keys
                                                 hons-assoc-equal)
                           (;sexpr-eval-4v-sexpr-restrict
                            ;4v-sexpr-restrict-4v-sexpr-restrict
                            4v-sexpr-restrict-alist
                            4v-sexpr-eval 4v-sexpr-restrict
                            default-car default-cdr))
           :do-not-induct t)
          (witness :ruleset 4v-sexpr-fixpointp-witnessing)
          (witness :ruleset 4v-sexpr-equiv-witnessing))
  :otf-flg t)



(defquant 4v-sexpr-fixpoint-lower-boundp (ups lb)
  (forall (fp env)
          (implies (and (keys-equiv ups fp)
                        (4v-alist-<= ;; 4v-env-equiv
                         (4v-sexpr-eval-alist ups (make-fal fp env))
                                      fp))
                   (4v-alist-<= (4v-sexpr-eval-alist lb env) fp))))

(verify-guards 4v-sexpr-fixpoint-lower-boundp)

(defun 4v-sexpr-fixpointp-strong (ups fixpoint)
  (declare (xargs :guard t))
  (and (4v-sexpr-fixpointp ups fixpoint)
       (keys-equiv ups fixpoint)
       (not (intersectp-equal (alist-keys ups)
                              (4v-sexpr-vars-list (alist-vals fixpoint))))))

;; This was my previous definition for a fixpoint lower bound.  However, it's
;; not quite strong enough.  The previous definition implies this one (as we'll
;; prove.)
(defquant 4v-sexpr-fixpoint-lower-boundp2 (ups vals)
  (forall fixpoint (implies (4v-sexpr-fixpointp-strong ups fixpoint)
                            (4v-sexpr-alist-<= vals fixpoint))))










(defun 4v-sexpr-fixpointp-alt1 (ups fp)
  (4v-sexpr-alist-equiv (4v-sexpr-restrict-alist ups fp)
                        fp))

(defthmd 4v-sexpr-alist-equiv-fixpoint
  (implies (and (4v-sexpr-fixpointp ups fixpoint)
                (keys-equiv ups fixpoint))
           (4v-sexpr-alist-equiv (4v-sexpr-restrict-alist ups fixpoint)
                                 fixpoint))
  :hints ((witness :ruleset
                   (4v-sexpr-alist-equiv-witnessing
                    4v-sexpr-fixpointp-hons-assoc-equal-ex))))


(defthm 4v-sexpr-fixpointp-is-alt1
  (implies (keys-equiv ups fixpoint)
           (iff (4v-sexpr-fixpointp ups fixpoint)
                (4v-sexpr-fixpointp-alt1 ups fixpoint)))
  :hints(("Goal" :in-theory (enable 4v-sexpr-alist-equiv-fixpoint)
          :do-not-induct t)
         (witness :ruleset (4v-sexpr-fixpointp-witnessing
                            4v-sexpr-alist-equiv-example))))

(defexample 4v-sexpr-fixpoint-lower-boundp-eval-alist-ex
  :pattern (4v-sexpr-eval-alist x (append fp env))
  :templates (fp env)
  :instance-rulename 4v-sexpr-fixpoint-lower-boundp-instancing)




(defthm 4v-sexpr-fixpoint-lower-boundp2-if-lower-boundp
  (implies (4v-sexpr-fixpoint-lower-boundp ups lb)
           (4v-sexpr-fixpoint-lower-boundp2 ups lb))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (4v-sexpr-alist-equiv-is-alt
                            4v-sexpr-alist-<=-is-alt)
                           (4v-sexpr-eval)))
          (witness :ruleset (4v-sexpr-fixpoint-lower-boundp-witnessing
                             4v-sexpr-fixpoint-lower-boundp2-witnessing))
          (witness :ruleset (4v-sexpr-alist-<=-alt-witnessing
                             4v-sexpr-alist-<=-alt-eval-alist-ex))
          (witness :ruleset 4v-sexpr-alist-equiv-alt-eval-alist-ex)
;;           (witness :ruleset 4v-sexpr-<=-witnessing)
          (and stable-under-simplificationp
               '(:use ((:instance 4v-sexpr-fixpoint-lower-boundp-necc
                                  (fp (4v-sexpr-eval-alist fixpoint0 env0))
                                  (env env0)))))
          )
  :otf-flg t)




(defthm lower-boundp-nil-for-no-update-fns
  (4v-sexpr-fixpoint-lower-boundp ups nil)
  :hints (("goal" :do-not-induct t
           :in-theory (disable 4v-sexpr-eval))
          (witness :ruleset (4v-sexpr-fixpoint-lower-boundp-witnessing))))




(defcong 4v-sexpr-alist-equiv iff (4v-sexpr-fixpoint-lower-boundp ups lb) 1
  :hints (("goal" :do-not-induct t
           :in-theory (disable 4v-sexpr-eval))
          (witness :ruleset (4v-sexpr-fixpoint-lower-boundp-witnessing))
          (witness :ruleset (4v-sexpr-fixpoint-lower-boundp-eval-alist-ex))
          ))

(defthm 4v-sexpr-alist-equiv-nil-any-atom
  (implies (atom x)
           (equal (4v-sexpr-alist-equiv x nil) t))
  :hints (("goal" :do-not-induct t)
          (witness :ruleset 4v-sexpr-alist-equiv-witnessing))
  :rule-classes nil)

(defthm 4v-sexpr-fixpoint-lower-boundp-atom-ups
  (implies (and (syntaxp (not (equal ups ''nil)))
                (atom ups))
           (iff (4v-sexpr-fixpoint-lower-boundp ups lb)
                (4v-sexpr-fixpoint-lower-boundp nil lb)))
  :hints (("goal" :use ((:instance 4v-sexpr-alist-equiv-nil-any-atom
                                   (x ups))))))


(defthm lower-boundp-when-atom-car
  (implies (and (not (4v-sexpr-fixpoint-lower-boundp ups lb))
                (not (consp (car ups))))
           (not (4v-sexpr-fixpoint-lower-boundp (cdr ups) lb)))
  :hints (("goal" :do-not-induct t
           :in-theory (disable 4v-sexpr-eval)
           :cases ((consp ups)))
          (witness :ruleset (4v-sexpr-fixpoint-lower-boundp-witnessing))
          (witness :ruleset (4v-sexpr-fixpoint-lower-boundp-eval-alist-ex))
          )
  :otf-flg t)












(defthm alist-keys-4v-sexpr-fixpoint-spec
  (equal (alist-keys (4v-sexpr-fixpoint-spec ups))
         (alist-keys ups))
  :hints (("goal" :induct t)))

;; (defthm keys-equiv-4v-sexpr-eval-alist
;;   (keys-equiv (4v-sexpr-eval-alist al env)
;;               (double-rewrite al))
;;   :hints(("Goal" :in-theory (enable keys-equiv-iff-set-equiv-alist-keys))))

;; (defthm keys-equiv-4v-sexpr-fixpoint-spec
;;   (keys-equiv (4v-sexpr-fixpoint-spec ups)
;;               (double-rewrite ups))
;;   :hints(("Goal" :in-theory (enable keys-equiv-iff-set-equiv-alist-keys))))

;; (defcong keys-equiv keys-equiv (cons a b) 2
;;   :hints (("goal" :do-not-induct t)
;;           (witness)))



;; (local
;;  (progn
;;    (defthmd replace-fixpoint-in-hons-assoc-equal
;;      (implies (key-and-env-equiv (cons (cons k v) a) b)
;;               (4v-equiv (cdr (hons-assoc-equal k b))
;;                         v)))

;;    (defthm 4v-<=-cons-append-env
;;      (implies (and (4v-alist-<= (cons (cons k v) a) fp0)
;;                    (keys-equiv (double-rewrite (cons (cons k v) a)) fp0))
;;               (4v-<=
;;                (4v-sexpr-eval
;;                 x (cons (cons k v) (append a env)))
;;                (4v-sexpr-eval
;;                 x (append fp0 env))))
;;      :hints (("goal" :use ((:instance 4v-alist-<=-append
;;                                       (a (cons (cons k v) a))
;;                                       (b fp0)
;;                                       (c env) (d env)))
;;               :do-not-induct t
;;               :in-theory (disable 4v-alist-<=-append 4v-fix 4v-<=)))
;;      :otf-flg t)

;;    (defthm keys-equiv-cons-caar
;;      (implies (consp (car x))
;;               (keys-equiv (cons (cons (caar x) v) (cdr x))
;;                           (double-rewrite x))))

;;    (defthm key-and-env-equiv-remove-assoc-hons
;;      (implies (and (not (4v-env-equiv a (remove-assoc-hons k b)))
;;                    (not (hons-assoc-equal k a)))
;;               (not (key-and-env-equiv (cons (cons k v) a) b)))
;;      :hints (("goal" :do-not-induct t
;;               :in-theory (e/d (key-and-env-equiv)
;;                               (4v-fix
;;                                4v-env-equiv-to-key-and-env-equiv)))
;;              (witness :ruleset 4v-env-equiv-witnessing)
;;              (witness :ruleset 4v-env-equiv-hons-assoc-equal-ex))
;;      :otf-flg t)


;;    (defthm keys-equiv-cons-eval-alist
;;      (implies (and (keys-equiv ups fp0)
;;                    (consp (car ups)))
;;               (equal (keys-equiv (cons (cons (caar ups) v)
;;                                        (4v-sexpr-eval-alist (cdr ups) a))
;;                                  fp0)
;;                      t))
;;      :hints (("goal" :in-theory (enable keys-equiv-iff-set-equiv-alist-keys))))



;;    (defthmd 4v-alist-<=-acons->remove
;;      (implies (not (hons-assoc-equal k a))
;;               (iff (4v-alist-<= (cons (cons k v) a) b)
;;                    (and (4v-<= v (4v-lookup k b))
;;                         (4v-alist-<= a (remove-assoc-hons k b)))))
;;      :hints (("goal" :do-not-induct t
;;               :in-theory (disable 4v-fix))
;;              (witness :ruleset 4v-alist-<=-witnessing)
;;              (witness :ruleset 4v-alist-<=-hons-assoc-equal-example))
;;      :otf-flg t)

;;    (defthm hack
;;      (implies
;;       (and
;;        (4v-alist-<=
;;         (4v-sexpr-eval-alist (4v-sexpr-fixpoint-spec (cdr update-fns))
;;                              (cons (cons (caar update-fns)
;;                                          (cdr (hons-assoc-equal (caar update-fns)
;;                                                                 fp0)))
;;                                    env0))
;;         (remove-assoc-hons (caar update-fns) fp0))
;;        (consp update-fns)
;;        (consp (car update-fns))
;;        (4v-sexpr-fixpoint-lower-boundp (cdr update-fns)
;;                                        (4v-sexpr-fixpoint-spec (cdr update-fns)))
;;        (not (hons-assoc-equal (caar update-fns)
;;                               (cdr update-fns)))
;;        (no-duplicatesp-equal (alist-keys (cdr update-fns)))
;;        (keys-equiv update-fns fp0)
;;        (key-and-env-equiv (cons (cons (caar update-fns)
;;                                       (4v-sexpr-eval (cdar update-fns)
;;                                                      (append fp0 env0)))
;;                                 (4v-sexpr-eval-alist (cdr update-fns)
;;                                                      (append fp0 env0)))
;;                           fp0))
;;       (4v-<=
;;        (4v-sexpr-eval
;;         (cdar update-fns)
;;         (cons
;;          (cons (caar update-fns) 'x)
;;          (append (4v-sexpr-eval-alist (4v-sexpr-fixpoint-spec (cdr update-fns))
;;                                       (cons (cons (caar update-fns) 'x) env0))
;;                  env0)))
;;        (CDR (HONS-ASSOC-EQUAL (CAAR UPDATE-FNS)
;;                               FP0))))
;;      :hints (("goal" :do-not-induct t
;;               :in-theory (e/d (alist-keys
;;                                4v-alist-<=-acons->remove
;;                                4v-alist-<=-trans2
;;                                replace-fixpoint-in-hons-assoc-equal)
;;                               (4v-sexpr-restrict-alist
;;                                4v-sexpr-eval
;;                                4v-alist-<=-acons-1
;;                                4v-fix 4v-<=)))))))

(defthmd 4v-alist-<=-acons->remove
     (implies (not (hons-assoc-equal k a))
              (iff (4v-alist-<= (cons (cons k v) a) b)
                   (and (4v-<= v (4v-lookup k b))
                        (4v-alist-<= a (remove-assoc-hons k b)))))
     :hints (("goal" :do-not-induct t
              :in-theory (disable 4v-fix))
             (witness :ruleset 4v-alist-<=-witnessing)
             (witness :ruleset 4v-alist-<=-hons-assoc-equal-example))
     :otf-flg t)




;; Notation: We'll use
;; -    * to apply a substitution (aka 4v-sexpr-restrict(-alist))
;; -    : to construct a substitution pair
;; -    :: to append substitutions.
;; -    \ to remove a binding from a substitution

;; Sketch of proof that we compute a least fixpoint:
;; Induct on length of update-fns.  Base case is trivial.
;; In the inductive case, let update-fns = ((s1 : up1) :: upsr), i.e. s1
;; is the first signal bound and up1 is its update function.  By IH we
;; have computed lbr, lower bound for upsr.  Meaning, for any fpr, envr
;; where fpr has the same keys as upsr and satisfying
;; upsr (fpr :: envr) <= fpr,
;; we have lbr(envr) <= fpr.

;; Our result is:
;; lbf = (s1 : ((up1 * lbr) * (s1 : X)))
;;        :: (lbr * (s1 : ((up1 * lbr) * (s1 : X)))).

;; We need to show that for any fp, env where the bound signals of fp are
;; the same as those of ups and ups (fp :: env) <= fp,
;; we have lbf(env) <= fp.

;; Suppose we have such an fp, env.  Decomposing, we have
;; upsr (fp :: env) <= fp\s1, and
;; up1 (fp :: env)  <= s1(fp).

;; and we need to show
;; ((up1 * lbr) * (s1 : X))(env) <= s1(fp) and
;; (lbr * (s1 : ((up1 * lbr) * (s1 : X)))) (env) <= fp\s1.


;; Evaluation rule for substitution (4v-sexpr-eval-4v-sexpr-restrict(-alist)):
;; (a * b)(env) = a(b(env) :: env).

;; So we reduce the above obligations to:
;; (up1 * lbr)((s1 : X) :: env)
;; = up1(lbr((s1 : X) :: env) :: (s1 : X) :: env) <= s1(fp)
;; and
;; lbr ((s1 : ((up1 * lbr) * (s1 : X)) (env)) :: env) =
;; lbr ((s1 : up1(lbr((s1 : X) :: env) :: (s1 : X) :: env)) :: env) <= s1\fp1.

;; Looking at the second obligation, we need to show
;; lbr ((s1 : up1(lbr((s1 : X) :: env) :: (s1 : X) :: env)) :: env) <= s1\fp1.
;;
;; Using the IH, let fpr, envr as above be fp\s1 and
;; ((s1 : up1(lbr((s1 : X) :: env) :: (s1 : X) :: env)) :: env).
;; If we can show
;; upsr (fpr :: envr) <= fpr, i.e.
;; upsr (fp\s1 :: (s1 : up1(lbr((s1 : X) :: env) :: (s1 : X) :: env)) :: env) <= fp\s1,
;; then we have lbr(envr) <= fpr, i.e.
;; lbr ((s1 : up1(lbr((s1 : X) :: env) :: (s1 : X) :: env)) :: env) <= fp\s1,
;; and we'll be done.

;; But we already know
;; upsr (fp :: env) <= fp\s1.  By monotonicity of upsr and transitivity
;; of <=, we can just show
;; fp\s1 :: (s1 : up1(lbr((s1 : X) :: env) :: (s1 : X) :: env)) <= fp.
;; This decomposes to:
;; fp\s1 <= fp\s1 (trivial)
;; and up1(lbr((s1 : X) :: env) :: (s1 : X) :: env) <= s1(fp),
;; which is just the first obligation above.

;; Looking at the first obligation, we need to show
;; up1(lbr((s1 : X) :: env) :: (s1 : X) :: env) <= s1(fp)m
;; but we have
;; up1 (fp :: env) <= s1(fp).  It suffices to show that
;; up1(lbr((s1 : X) :: env) :: (s1 : X) :: env) has the
;; same keys as fp (trivial) and ... <= fp.
;; That is,
;; lbr ((s1 : X) :: env) :: (s1 : X) <= fp,
;; which decomposes to
;; X <= s1(fp), (trivial),
;; and
;; lbr ((s1 : X) :: env) <= fp\s1.

;; Here we apply the IH again: let fpr, envr as above be fp\s1 and
;; ((s1 : X) :: env).
;; If we can show
;; upsr (fpr :: envr) <= fpr, i.e.
;; upsr (fp\s1 :: (s1 : X) :: env) <= fp\s1,
;; then we have lbr(envr) <= fpr, i.e.
;; lbr ((s1 : X) :: env) <= fp\s1,
;; and we'll be done.

;; But we already know
;; upsr (fp :: env) <= fp\s1.  By monotonicity of upsr and transitivity
;; of <=, we can just show
;; fp\s1 :: (s1 : X) <= fp.
;; This decomposes to:
;; fp\s1 <= fp\s1 (trivial)
;; and X <= s1(fp), also trivial.


;; Working from bottom up:
(defthm |fp\s1 :: (s1 : X) <= fp|
  (4v-alist-<= (append (remove-assoc-hons s1 fp)
                       (list (cons s1 *4vx*)))
               fp)
  :hints ((witness :ruleset 4v-alist-<=-witnessing)))

(defthmd 4v-alist-<=-append-cons-append
  (implies (and (set-equiv (double-rewrite (cons bk (alist-keys a)))
                            (double-rewrite (alist-keys d)))
                (4v-alist-<= (append a (list (cons bk bv)))
                             d)
                (4v-alist-<= c e))
           (4v-alist-<= (append a (cons (cons bk bv) c))
                        (append d e)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d* (hons-assoc-equal-iff-member-alist-keys
;; hons-assoc-equal-when-not-member-alist-keys
                             )
                            (alist-keys-member-hons-assoc-equal
                             4v-fix 4v-<= default-car default-cdr
                             append member-when-atom member-equal
                             alist-keys-when-atom
                             ;; set-equiv-asym set-equiv-trans
                             (:rules-of-class :type-prescription :here))))
          (witness :ruleset (4v-alist-<=-witnessing
                             4v-alist-<=-4v-lookup-example))
          (witness :ruleset set-equiv-member-template)))


;(why 4v-alist-<=-trans2)
;(why 4V-ALIST-<=-SEXPR-EVAL-ALIST-MONOTONIC-ENV)
;(why 4v-alist-<=-append-cons-append)


;; Assuming
;; upsr (fp :: env) <= fp\s1,
;; prove
;; upsr (fp\s1 :: (s1 : X) :: env) <= fp\s1.
(defthm |upsr (fp\s1 :: (s1 : X) :: env) <= fp\s1|
  (implies (and (4v-alist-<= (4v-sexpr-eval-alist upsr (append fp env))
                             (remove-assoc-hons s1 fp))
                (set-equiv (alist-keys fp)
                            (cons s1 (alist-keys upsr))))
           (4v-alist-<= (4v-sexpr-eval-alist upsr
                                             (append (remove-assoc-hons s1 fp)
                                                     (cons (cons s1 *4vx*)
                                                           env)))
                        (remove-assoc-hons s1 fp)))
  :hints(("Goal" :in-theory
          (e/d (4v-alist-<=-trans2
                hons-assoc-equal-iff-member-alist-keys
                set-equiv-breakdown-cons
                4v-alist-<=-append-cons-append)
               (switch-append-cons
                switch-append
                alist-keys-member-hons-assoc-equal))
          :do-not-induct t)))



;; Given
;; upsr (fp :: env) <= fp\s1
;; and lbr a FLB of upsr,
;; show
;; lbr ((s1 : X) :: env) <= fp\s1.
(defthm |lbr ((s1 : X) :: env) <= fp\s1|
  (implies (and (4v-sexpr-fixpoint-lower-boundp upsr lbr)
                (4v-alist-<=
                 (4v-sexpr-eval-alist upsr (append fp env))
                 (remove-assoc-hons s1 fp))
                (set-equiv (alist-keys fp)
                            (cons s1 (alist-keys upsr)))
                (not (member-equal s1 (alist-keys upsr))))
           (4v-alist-<=
            (4v-sexpr-eval-alist
             lbr
             (cons (cons s1 *4vx*) env))
            (remove-assoc-hons s1 fp)))
  :hints (("goal" :use
           ((:instance 4v-sexpr-fixpoint-lower-boundp-necc
                       (ups upsr)
                       (lb lbr)
                       (fp (remove-assoc-hons s1 fp))
                       (env (cons (cons s1 *4vx*) env))))
           :in-theory (e/d (set-equiv-breakdown-cons)
                           (alist-keys-member-hons-assoc-equal
                            switch-append
                            switch-append-cons))
           :do-not-induct t))
  :otf-flg t)




;; Looking at the first obligation, we need to show
;; up1(lbr((s1 : X) :: env) :: (s1 : X) :: env) <= s1(fp)
;; but we have
;; up1 (fp :: env) <= s1(fp).  It suffices to show that "..." has the
;; same keys as fp (trivial) and ... <= fp.
;; That is,
;; lbr ((s1 : X) :: env) :: (s1 : X) <= fp,
;; which decomposes to
;; lbr ((s1 : X) :: env) <= fp\s1 (same as the second obligation above)
;; and
;; X <= s1(fp), trivial.

(defthm |lbr ((s1 : X) :: env) :: (s1 : X) <= fp|
  (implies (4v-alist-<=
            (4v-sexpr-eval-alist
             lbr (cons (cons s1 *4vx*) env))
            (remove-assoc-hons s1 fp))
           (4v-alist-<=
            (append (4v-sexpr-eval-alist
                     lbr (cons (cons s1 *4vx*) env))
                    (list (cons s1 *4vx*)))
            fp))
  :hints (("goal" :do-not-induct t
           :in-theory (disable 4v-fix 4v-sexpr-eval))
          (witness :ruleset (4v-alist-<=-witnessing
                             4v-alist-<=-4v-lookup-example))))

;; given lbr ((s1 : X) :: env) <= fp\s1
;; and up1 (fp :: env) <= s1(fp),
;; show up1(lbr((s1 : X) :: env) :: (s1 : X) :: env) <= s1(fp).

(defthm |up1(lbr((s1 : X) :: env) :: (s1 : X) :: env) <= s1(fp)|
  (implies (and (4v-alist-<=
                 (4v-sexpr-eval-alist
                  lbr (cons (cons s1 *4vx*) env))
                 (remove-assoc-hons s1 fp))
                (4v-<= (4v-sexpr-eval up1 (append fp env))
                       (4v-lookup s1 fp))
                (set-equiv (alist-keys fp)
                            (cons s1 (alist-keys lbr))))
           (4v-<=
            (4v-sexpr-eval
             up1
             (append (4v-sexpr-eval-alist
                      lbr (cons (cons s1 *4vx*) env))
                     (cons (cons s1 *4vx*) env)))
            (4v-lookup s1 fp)))
  :hints (("goal" :in-theory
           (e/d (4v-<=-trans2
                 4v-alist-<=-append-cons-append)
                (4v-<= switch-append
                       switch-append-cons 4v-lookup))
           :do-not-induct t)))



(defthmd 4v-alist-<=-append->remove
     (implies (not (hons-assoc-equal k a))
              (iff (4v-alist-<= (append a (list (cons k v))) b)
                   (and (4v-<= v (4v-lookup k b))
                        (4v-alist-<= a (remove-assoc-hons k b)))))
     :hints (("goal" :do-not-induct t
              :in-theory (disable 4v-fix))
             (witness :ruleset 4v-alist-<=-witnessing)
             (witness :ruleset 4v-alist-<=-hons-assoc-equal-example))
     :otf-flg t)

;; But we already know
;; upsr (fp :: env) <= fp\s1.  By monotonicity of upsr and transitivity
;; of <=, we can just show
;; fp\s1 :: (s1 : up1(lbr((s1 : X) :: env) :: (s1 : X) :: env)) <= fp.
;; This decomposes to:
;; fp\s1 <= fp\s1 (trivial)
;; and up1(lbr((s1 : X) :: env) :: (s1 : X) :: env) <= s1(fp),
;; which is just the first obligation above.

(defthm
  |upsr (fp\s1 :: (s1 : up1(lbr((s1 : X) :: env) :: (s1 : X) :: env)) :: env) <= fp\s1|
  (implies (and (4v-alist-<=
                 (4v-sexpr-eval-alist upsr (append fp env))
                 (remove-assoc-hons s1 fp))
                (4v-<= (4v-sexpr-eval up1 (append fp env))
                       (4v-lookup s1 fp))
                (set-equiv (alist-keys fp)
                            (cons s1 (alist-keys upsr)))
                (set-equiv (alist-keys lbr)
                            (alist-keys upsr))
                (not (member-equal s1 (alist-keys upsr)))
                (4v-sexpr-fixpoint-lower-boundp upsr lbr))
           (4v-alist-<=
            (4v-sexpr-eval-alist
             upsr
             (append (remove-assoc-hons s1 fp)
                     (cons (cons s1 (4v-sexpr-eval
                                     up1
                                     (append (4v-sexpr-eval-alist
                                              lbr
                                              (cons (cons s1 *4vx*) env))
                                             (cons (cons s1 *4vx*)
                                                   env))))
                           env)))
            (remove-assoc-hons s1 fp)))
  :hints(("Goal" :in-theory
          (e/d (4v-alist-<=-trans2
                hons-assoc-equal-iff-member-alist-keys
                set-equiv-breakdown-cons
                set-equiv-breakdown-cons2
                4v-alist-<=-append->remove
                4v-alist-<=-append-cons-append)
               (switch-append-cons
                switch-append 4v-<= 4v-fix 4v-lookup
                alist-keys-member-hons-assoc-equal))
          :do-not-induct t)))


;; Using the IH, let fpr, envr as above be fp\s1 and
;; ((s1 : up1(lbr((s1 : X) :: env) :: (s1 : X) :: env)) :: env).
;; If we can show
;; upsr (fpr :: envr) <= fpr, i.e.
;; upsr (fp\s1 :: (s1 : up1(lbr((s1 : X) :: env) :: (s1 : X) :: env)) :: env) <= fp\s1,
;; then we have lbr(envr) <= fpr, i.e.
;; lbr ((s1 : up1(lbr((s1 : X) :: env) :: (s1 : X) :: env)) :: env) <= fp\s1,
;; and we'll be done.


(defthm |lbr ((s1 : up1(lbr((s1 : X) :: env) :: (s1 : X) :: env)) :: env) <= fp\s1|
  (implies (and (4v-alist-<=
                 (4v-sexpr-eval-alist upsr (append fp env))
                 (remove-assoc-hons s1 fp))
                (4v-<= (4v-sexpr-eval up1 (append fp env))
                       (4v-lookup s1 fp))
                (set-equiv (alist-keys fp)
                            (cons s1 (alist-keys upsr)))
                (set-equiv (alist-keys lbr)
                            (alist-keys upsr))
                (not (member-equal s1 (alist-keys upsr)))
                (4v-sexpr-fixpoint-lower-boundp upsr lbr))
           (4v-alist-<=
            (4v-sexpr-eval-alist
             lbr
             (cons (cons s1 (4v-sexpr-eval
                             up1
                             (append (4v-sexpr-eval-alist
                                      lbr
                                      (cons (cons s1 *4vx*) env))
                                     (cons (cons s1 *4vx*)
                                           env))))
                   env))
            (remove-assoc-hons s1 fp)))
  :hints (("goal" :use ((:instance 4v-sexpr-fixpoint-lower-boundp-necc
                                   (ups upsr)
                                   (lb lbr)
                                   (fp (remove-assoc-hons s1 fp))
                                   (env (cons (cons s1 (4v-sexpr-eval
                                                        up1
                                                        (append (4v-sexpr-eval-alist
                                                                 lbr
                                                                 (cons (cons s1 *4vx*) env))
                                                                (cons (cons s1 *4vx*)
                                                                      env))))
                                              env))))
           :in-theory
           (e/d (4v-alist-<=-trans2
                 hons-assoc-equal-iff-member-alist-keys
                 set-equiv-breakdown-cons
                 set-equiv-breakdown-cons2
                 4v-alist-<=-append->remove
                 4v-alist-<=-append-cons-append)
                (switch-append-cons
                 switch-append 4v-<= 4v-fix 4v-lookup
                 alist-keys-member-hons-assoc-equal)))))


;; Our result is:
;; lbf = (s1 : ((up1 * lbr) * (s1 : X)))
;;        :: (lbr * (s1 : ((up1 * lbr) * (s1 : X)))).
(defthm inductive-step
  (implies (and (4v-sexpr-fixpoint-lower-boundp upsr lbr)
                (set-equiv (alist-keys upsr)
                            (alist-keys lbr))
                (not (member-equal s1 (alist-keys upsr))))
           (4v-sexpr-fixpoint-lower-boundp
            (cons (cons s1 up1) upsr)
            (cons (cons s1 (4v-sexpr-restrict
                            (4v-sexpr-restrict up1 lbr)
                            (list (cons s1
                                        *4vx-sexpr*))))
                  (4v-sexpr-restrict-alist
                   lbr (list (cons s1 (4v-sexpr-restrict
                                       (4v-sexpr-restrict up1 lbr)
                                       (list (cons s1
                                                   *4vx-sexpr*)))))))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (4v-alist-<=-acons->remove
                            keys-equiv-iff-set-equiv-alist-keys
                            hons-assoc-equal-iff-member-alist-keys)
                           (4v-<= 4v-fix 4v-lookup
                                  switch-append switch-append-cons
                                  alist-keys-member-hons-assoc-equal
                                  4v-sexpr-eval)))
          (witness :ruleset 4v-sexpr-fixpoint-lower-boundp-witnessing))
  :otf-flg t)



(defthm 4v-sexpr-fixpoint-lower-boundp-4v-sexpr-fixpoint-spec
  (implies (no-duplicatesp-equal (alist-keys update-fns))
           (4v-sexpr-fixpoint-lower-boundp
            update-fns
            (4v-sexpr-fixpoint-spec update-fns)))
  :hints (("goal" :induct t
           :in-theory (disable 4v-sexpr-restrict-4v-sexpr-restrict))))

(defthm 4v-sexpr-fixpoint-lower-boundp2-4v-sexpr-fixpoint-spec
  (implies (no-duplicatesp-equal (alist-keys update-fns))
           (4v-sexpr-fixpoint-lower-boundp2
            update-fns
            (4v-sexpr-fixpoint-spec update-fns))))














;; (defthm 4v-sexpr-fixpoint-lower-boundp-4v-sexpr-fixpoint-spec
;;   (implies (no-duplicatesp-equal (alist-keys update-fns))
;;            (4v-sexpr-fixpoint-lower-boundp
;;             update-fns
;;             (4v-sexpr-fixpoint-spec update-fns)))
;;   :hints (("goal" :induct (4v-sexpr-fixpoint-spec update-fns)
;;            :in-theory (e/d (alist-keys
;;                             4v-alist-<=-acons->remove
;;                             4v-alist-<=-trans2)
;;                            (4v-sexpr-restrict-alist
;;                             4v-sexpr-eval
;;                             4v-sexpr-restrict
;;                             4v-alist-<=-acons-1
;;                             default-car default-cdr
;;                             keys-equiv-when-alist-keys
;;                             subsetp-car-member
;;                             member-equal
;;                             4v-fix 4v-<=))
;;            :do-not-induct t)
;;           (witness :ruleset 4v-sexpr-fixpoint-lower-boundp-witnessing)
;;           (and stable-under-simplificationp
;;                '(:use ((:instance 4v-sexpr-fixpoint-lower-boundp-necc
;;                                   (ups (cdr update-fns))
;;                                   (fp (remove-assoc-hons (caar update-fns) fp0))
;;                                   (env (cons (cons (caar update-fns)
;;                                                    (cdr (hons-assoc-equal
;;                                                          (caar update-fns)
;;                                                          fp0)))
;;                                              env0))
;;                                   (lb (4v-sexpr-fixpoint-spec
;;                                        (cdr update-fns))))))))
;;   :otf-flg t)










;; (defthmd 4v-sexpr-fixpointp-iff-4v-sexpr-alist-equiv
;;   (implies (keys-equiv ups fixpoint)
;;            (iff (4v-sexpr-fixpointp ups fixpoint)
;;                 (4v-sexpr-alist-equiv (4v-sexpr-restrict-alist ups fixpoint)
;;                                       fixpoint)))
;;   :hints(("Goal" :in-theory (enable 4v-sexpr-alist-equiv-fixpoint)
;;           :do-not-induct t)
;;          (witness :ruleset (4v-sexpr-fixpointp-witnessing
;;                             4v-sexpr-alist-equiv-example))))


