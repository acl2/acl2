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
(include-book "sexpr-fixpoint-spec")
(local (include-book "centaur/misc/hons-sets" :dir :system))

(local (in-theory (disable set::double-containment)))

;;

(defun 4v-sexpr-fixpoint-spec-without-xes (ups)
  (if (atom ups)
      nil
    (b* ((rest (4v-sexpr-fixpoint-spec-without-xes (cdr ups)))
         ((when (atom (car ups))) rest)
         (name (caar ups))
         (upfn (cdar ups))
         (composed-with-rest
          (4v-sexpr-restrict upfn rest))
         ;; (fixpoint (4v-sexpr-restrict composed-with-rest
;;                                    `((,name x))))
         (rest-restrict (4v-sexpr-restrict-alist
                         rest `((,name . ,composed-with-rest)))))
      (acons name composed-with-rest rest-restrict))))

(defthm hons-assoc-equal-4v-sexpr-fixpoint-spec-without-xes
  (iff (hons-assoc-equal k (4v-sexpr-fixpoint-spec-without-xes ups))
       (hons-assoc-equal k ups)))

(defthm alist-keys-4v-sexpr-fixpoint-spec-without-xes
  (equal (alist-keys (4v-sexpr-fixpoint-spec-without-xes ups))
         (alist-keys ups)))


(defthm 4v-sexpr-alist-equiv-acons
  (implies (and (not (hons-assoc-equal k r1))
                (not (hons-assoc-equal k r2)))
           (iff (4v-sexpr-alist-equiv (cons (cons k v1) r1)
                                      (cons (cons k v2) r2))
                (and (4v-sexpr-equiv v1 v2)
                     (4v-sexpr-alist-equiv r1 r2))))
  :hints (("goal" :do-not-induct t)
          (witness :ruleset 4v-sexpr-alist-equiv-witnessing)
          (witness :ruleset 4v-sexpr-alist-equiv-example)))







(defthm 4v-sexpr-restrict-alist-4v-sexpr-restrict-alist
  (4v-sexpr-alist-equiv (4v-sexpr-restrict-alist (4v-sexpr-restrict-alist al env1)
                                              env2)
                        (4v-sexpr-restrict-alist al
                                              (append (4v-sexpr-restrict-alist
                                                       env1 env2) env2))))


(local
 (defthm 4v-sexpr-restrict-alist-hons-acons-each-4vx-sexpr
   (equal (4v-sexpr-restrict-alist (hons-acons-each keys *4vx-sexpr* rest) al)
          (hons-acons-each keys *4vx-sexpr*
                           (4v-sexpr-restrict-alist rest al)))
   :hints(("Goal" :in-theory (enable hons-acons-each)))))


;; (local (defthm switch-append
;;          (implies (not (hons-assoc-equal x al))
;;                   (alist-equiv (append al (list (cons x v)))
;;                                (cons (cons x v) al)))
;;          :hints (("goal" :in-theory (enable
;;                                      alist-equiv-iff-agree-on-bad-guy)))))

(local (defthm switch-append-cons
         (implies (not (hons-assoc-equal x al))
                  (alist-equiv (append al (cons (cons x v) al2))
                               (cons (cons x v) (append al al2))))
         :hints (("goal" :in-theory (enable alist-equiv-iff-agree-on-bad-guy)))))

(local (defthm append-masking-alists
         (implies (subsetp-equal (alist-keys b) (alist-keys a))
                  (alist-equiv (append a b) a))
         :hints(("Goal" :in-theory (e/d (alist-equiv-iff-agree-on-bad-guy
                                         hons-assoc-equal-iff-member-alist-keys)
                                        (alist-keys-member-hons-assoc-equal))
                 :do-not-induct t)
                (set-reasoning)
                (and stable-under-simplificationp
                     '(:in-theory (e/d ()))))))

(local (defthm remove-masked-cons
         (alist-equiv (list* (cons k v1) (cons k v2) rest)
                      (cons (cons k v1) rest))
         :hints(("Goal" :in-theory (enable alist-equiv-iff-agree-on-bad-guy)))))

(defthm 4v-sexpr-fixpoint-spec-equiv-without-xes
  (implies (no-duplicatesp-equal (alist-keys ups))
           (4v-sexpr-alist-equiv
            (4v-sexpr-fixpoint-spec ups)
            (4v-sexpr-restrict-alist
             (4v-sexpr-fixpoint-spec-without-xes ups)
             (hons-acons-each (alist-keys ups) *4vx-sexpr* nil))))
  :hints (("goal" :induct (len ups)
           :do-not-induct t
           :in-theory (e/d (alist-keys hons-acons-each)
                           (4v-sexpr-fixpoint-spec
                            4v-sexpr-fixpoint-spec-without-xes
                            4v-sexpr-restrict default-car default-cdr))
           :expand ((4v-sexpr-fixpoint-spec ups)
                    (4v-sexpr-fixpoint-spec-without-xes ups))))
  :otf-flg t)









(defthm-4v-sexpr-flag
  (defthm 4v-sexpr-restrict-empty-alist
    (implies (atom al)
             (4v-sexpr-equiv (4v-sexpr-restrict x al) x))
    :flag sexpr)
  (defthm 4v-sexpr-restrict-list-empty-alist
    (implies (atom al)
             (4v-sexpr-list-equiv (4v-sexpr-restrict-list x al) x))
    :flag sexpr-list)
  :hints ((witness :ruleset 4v-sexpr-list-equiv-witnessing)))


(defthm-4v-sexpr-flag
  (defthm 4v-sexpr-restrict-remove-irrel-var
    (implies (not (member-equal k (4v-sexpr-vars x)))
             (equal (4v-sexpr-restrict x (cons (cons k v) al))
                    (4v-sexpr-restrict x al)))
    :flag sexpr)
  (defthm 4v-sexpr-restrict-list-remove-irrel-var
    (implies (not (member-equal k (4v-sexpr-vars-list x)))
             (equal (4v-sexpr-restrict-list x (cons (cons k v) al))
                    (4v-sexpr-restrict-list x al)))
    :flag sexpr-list))

(defthm-4v-sexpr-flag
  (defthm 4v-sexpr-restrict-with-rw-remove-irrel-var
    (implies (not (member-equal k (4v-sexpr-vars x)))
             (equal (4v-sexpr-restrict-with-rw x (cons (cons k v) al))
                    (4v-sexpr-restrict-with-rw x al)))
    :flag sexpr)
  (defthm 4v-sexpr-restrict-with-rw-list-remove-irrel-var
    (implies (not (member-equal k (4v-sexpr-vars-list x)))
             (equal (4v-sexpr-restrict-with-rw-list x (cons (cons k v) al))
                    (4v-sexpr-restrict-with-rw-list x al)))
    :flag sexpr-list))

(defthm-4v-sexpr-flag
  (defthm 4v-sexpr-restrict-alist-equiv
    (implies (alist-equiv a b)
             (equal (4v-sexpr-restrict x a)
                    (4v-sexpr-restrict x b)))
    :rule-classes :congruence
    :flag sexpr)
  (defthm 4v-sexpr-restrict-list-alist-equiv
    (implies (alist-equiv a b)
             (equal (4v-sexpr-restrict-list x a)
                    (4v-sexpr-restrict-list x b)))
    :rule-classes :congruence
    :flag sexpr-list))

(defthm-4v-sexpr-flag
  (defthm 4v-sexpr-restrict-with-rw-alist-equiv
    (implies (alist-equiv a b)
             (equal (4v-sexpr-restrict-with-rw x a)
                    (4v-sexpr-restrict-with-rw x b)))
    :rule-classes :congruence
    :flag sexpr)
  (defthm 4v-sexpr-restrict-with-rw-list-alist-equiv
    (implies (alist-equiv a b)
             (equal (4v-sexpr-restrict-with-rw-list x a)
                    (4v-sexpr-restrict-with-rw-list x b)))
    :rule-classes :congruence
    :flag sexpr-list))


(defquant sexpr-deptable-ok (deptable fixpoints)
  (forall (var sig)
          (implies
           (member-equal var (4v-sexpr-vars (cdr (hons-assoc-equal
                                               sig fixpoints))))
           (member-equal sig (cdr (hons-assoc-equal var deptable))))))





;; (defun sexpr-alist-deps-for-name (name al)
;;   (if (atom al)
;;       nil
;;     (if (or (atom (car al))
;;             (not (member-equal name (4v-sexpr-vars (cdar al)))))
;;         (sexpr-alist-deps-for-name name (cdr al))
;;       (cons (caar al) (sexpr-alist-deps-for-name name (cdr al))))))
(in-theory (disable hons-remove-duplicates))

;; (defthm member-hons-remove-duplicates1
;;   (iff (member-equal x (hons-remove-duplicates1 a b))
;;        (and (member-equal x a)
;;             (not (hons-assoc-equal x b)))))

;; (defthm member-hons-remove-duplicates
;;   (iff (member-equal x (hons-remove-duplicates a))
;;        (member-equal x a))
;;   :hints(("Goal" :in-theory (enable hons-remove-duplicates))))

;; (defthm set-equiv-hons-remove-duplicates
;;   (set-equiv (hons-remove-duplicates x)
;;               (double-rewrite x))
;;   :hints ((set-reasoning)))

;; (defthm no-duplicatesp-equal-hons-remove-duplicates1
;;   (no-duplicatesp-equal
;;    (hons-remove-duplicates1 a b)))

;; (defthm no-duplicatesp-equal-hons-remove-duplicates
;;   (no-duplicatesp-equal (hons-remove-duplicates x))
;;   :hints(("Goal" :in-theory (enable hons-remove-duplicates))))

(local

  (defthm hons-assoc-equal-sexpr-update-fixpoints
    (implies
     (no-duplicatesp-equal deps)
     (equal (hons-assoc-equal k (sexpr-update-fixpoints
                                 deps fixpoint restr-al))
            (if (and (member-equal k deps)
                     (hons-assoc-equal k fixpoint))
                (cons k (if *sexpr-fixpoint-rewrite*
                            (4v-sexpr-restrict-with-rw
                             (cdr (hons-assoc-equal k fixpoint))
                             restr-al)
                          (4v-sexpr-restrict
                             (cdr (hons-assoc-equal k fixpoint))
                             restr-al)))
              (hons-assoc-equal k fixpoint))))))

(encapsulate nil
  (local (defthm sexpr-update-fixpoints-when-empty-al
           (implies (not (consp al))
                    (4v-sexpr-alist-equiv
                     (sexpr-update-fixpoints deps al restr-al)
                     nil))
           :hints (("goal" :induct t)
                   (witness :ruleset 4v-sexpr-alist-equiv-witnessing))))

  (local (defthm sexpr-update-fixpoints-when-atom-car-al
           (implies (not (consp (car al)))
                    (4v-sexpr-alist-equiv
                     (sexpr-update-fixpoints deps (cdr al) restr-al)
                     (sexpr-update-fixpoints deps al restr-al)))
           :hints (("goal"
                    :in-theory (enable hons-assoc-equal)
                    :induct t)
                   (witness :ruleset 4v-sexpr-alist-equiv-witnessing))))

  (local (defthm hons-assoc-equal-sexpr-update-fixpoints-iff
           (iff (hons-assoc-equal k (sexpr-update-fixpoints deps fixpoint
                                                            restr-al))
                (hons-assoc-equal k fixpoint))))



  (local (defthm sexpr-update-fixpoints-when-member-caar-al-deps
           (implies (and (consp al)
                         (consp (car al))
                         (member-equal (caar al) deps)
                         (no-duplicatesp-equal deps))
                    (4v-sexpr-alist-equiv
                     (sexpr-update-fixpoints deps al restr-al)
                     (cons (cons (caar al)
                                 (4v-sexpr-restrict (cdar al) restr-al))
                           (sexpr-update-fixpoints deps (cdr al) restr-al))))
           :hints (("Goal"
                    :in-theory (enable hons-assoc-equal))
                   (witness :ruleset 4v-sexpr-alist-equiv-witnessing))))



  (defthm sexpr-update-fixpoints-when-deptable-ok
    (implies (sexpr-deptable-ok deptable fixpoints)
             (4v-sexpr-alist-equiv
              (sexpr-update-fixpoints
               (hons-remove-duplicates (cdr (hons-assoc-equal signame deptable)))
               fixpoints
               (list (cons signame val)))
              (4v-sexpr-restrict-alist fixpoints (list (cons signame val)))))
    :hints (("goal" :do-not-induct t
             :in-theory (disable sexpr-update-fixpoints))
            (witness :ruleset 4v-sexpr-alist-equiv-witnessing)
            (and stable-under-simplificationp
                 '(:use ((:instance sexpr-deptable-ok-necc
                                    (sig k0)
                                    (var signame))))))))

(defthm hons-assoc-equal-update-deptable
  (set-equiv (cdr (hons-assoc-equal k (update-deptable keys vals deptable)))
              (if (member-equal k keys)
                  (append vals (cdr (hons-assoc-equal k deptable)))
                (cdr (hons-assoc-equal k deptable)))))


(defexample sexpr-deptable-ok-ex
  :pattern (member-equal var (4v-sexpr-vars (cdr (hons-assoc-equal
                                               sig fixpoints))))
  :templates (var sig)
  :instance-rulename sexpr-deptable-ok-instancing)

(defexample sexpr-deptable-ok-ex2
  :pattern (member-equal sig (cdr (hons-assoc-equal var deptable)))
  :templates (var sig)
  :instance-rulename sexpr-deptable-ok-instancing)

(defthm find-sexpr-least-fixpoint-deptable-ok
  (b* (((mv fixpoints & deptable)
        (find-sexpr-least-fixpoint update-fns)))
    (sexpr-deptable-ok deptable fixpoints))
  :hints (("goal" :induct (len update-fns)
           :in-theory (disable sexpr-update-fixpoints 4v-sexpr-restrict
                               update-deptable
                               subsetp-car-member
                               default-car default-cdr
                               find-sexpr-least-fixpoint)
           :do-not-induct t
           :expand ((find-sexpr-least-fixpoint update-fns)))
          (witness :ruleset sexpr-deptable-ok-witnessing)
          (witness :ruleset sexpr-deptable-ok-ex)
          (witness :ruleset sexpr-deptable-ok-ex2))
  :otf-flg t)




(defthm find-sexpr-least-fixpoint-is-sexpr-fixpoint-spec-without-xes
  (4v-sexpr-alist-equiv
   (mv-nth 0 (find-sexpr-least-fixpoint update-fns))
   (4v-sexpr-fixpoint-spec-without-xes update-fns)))






(defthm alist-keys-find-sexpr-least-fixpoint-fixpoint
  (set-equiv (alist-keys (mv-nth 0 (find-sexpr-least-fixpoint update-fns)))
              (alist-keys update-fns)))


(defthm no-duplicatesp-equal-alist-keys-hons-shrink-alist
  (iff (no-duplicatesp-equal (alist-keys (hons-shrink-alist a b)))
       (no-duplicatesp-equal (alist-keys b))))

(local
 (encapsulate nil
   (local (defun find-key-with-var-bound (name al)
            (if (atom al)
                nil
              (if (member-equal name (4v-sexpr-vars (cdar al)))
                  (caar al)
                (find-key-with-var-bound name (Cdr al))))))


   (local (defthm no-duplicate-keys-implies-find-key-with-var-bound
            (implies (and (no-duplicatesp-equal (alist-keys b))
                          (member-equal var (4v-sexpr-vars-list (alist-vals b))))
                     (hons-assoc-equal (find-key-with-var-bound var b) b))
            :hints(("Goal" :in-theory (enable alist-keys alist-vals)))))

   (local (defthm
            member-4v-sexpr-vars-list-hons-assoc-equal-impl-member-find-key-with-var-bound
            (implies (no-duplicatesp-equal (alist-keys b))
                     (iff (member-equal var (4v-sexpr-vars-list (alist-vals b)))
                          (member-equal var (4v-sexpr-vars (cdr (hons-assoc-equal
                                                              (find-key-with-var-bound
                                                               var b)
                                                              b))))))
            :hints (("goal" :induct t))))

   (local (defthm not-member-vars-lookup-when-not-member-find-key-with-var-bound
            (implies (and (no-duplicatesp-equal (alist-keys b))
                          (not (member-equal var (4v-sexpr-vars (cdr
                                                              (hons-assoc-equal
                                                               (find-key-with-var-bound
                                                                var b)
                                                               b))))))
                     (not (member-equal var (4v-sexpr-vars (cdr (hons-assoc-equal k
                                                                               b))))))))



   (local (defthm not-member-vars-lookup-when-not-member-find-key-with-var-bound-corollary
            (implies (not (member-equal var (4v-sexpr-vars (cdr
                                                         (hons-assoc-equal
                                                          (find-key-with-var-bound
                                                           var
                                                           (hons-shrink-alist b nil))
                                                          b)))))
                     (not (member-equal var (4v-sexpr-vars (cdr (hons-assoc-equal k
                                                                               b))))))
            :hints (("goal" :use ((:instance
                                   not-member-vars-lookup-when-not-member-find-key-with-var-bound
                                   (b (hons-shrink-alist b nil))))
                     :in-theory (disable not-member-vars-lookup-when-not-member-find-key-with-var-bound)))))



   (defthm not-member-signame-vars-sexpr-update-fixpoints
     (implies (and (sexpr-deptable-ok deptable fixpoints)
                   (not (member-equal signame (4v-sexpr-vars val))))
              (not (member-equal signame
                                 (4v-sexpr-vars-list
                                  (alist-vals
                                   (hons-shrink-alist
                                    (sexpr-update-fixpoints
                                     (hons-remove-duplicates (cdr (hons-assoc-equal signame deptable)))
                                     fixpoints
                                     (list (cons signame val)))
                                    (list (cons signame val))))))))
     :hints (("goal"
              :in-theory (e/d (member-4v-sexpr-vars-list-hons-assoc-equal-impl-member-find-key-with-var-bound)
                              (sexpr-update-fixpoints
                               find-key-with-var-bound))
              :do-not-induct t)
             (and stable-under-simplificationp
                  '(:use ((:instance sexpr-deptable-ok-necc
                                     (sig (find-key-with-var-bound
                                           signame (hons-shrink-alist
                                                    (sexpr-update-fixpoints
                                                     (hons-remove-duplicates (cdr (hons-assoc-equal signame deptable)))
                                                     fixpoints
                                                     (list (cons signame val)))
                                                    (list (cons signame val)))))
                                     (var signame)))))))


    (defthm not-member-v-vars-sexpr-update-fixpoints
      (implies (and (sexpr-deptable-ok deptable fixpoints)
                    (not (member-equal v (4v-sexpr-vars val)))
                    (not (member-equal v (4v-sexpr-vars-list
                                          (alist-vals
                                           (hons-shrink-alist fixpoints nil))))))
               (not (member-equal v
                                  (4v-sexpr-vars-list
                                   (alist-vals
                                    (hons-shrink-alist
                                     (sexpr-update-fixpoints
                                      (hons-remove-duplicates (cdr (hons-assoc-equal signame deptable)))
                                      fixpoints
                                      (list (cons signame val)))
                                     (list (cons signame val))))))))
      :hints (("goal"
               :in-theory (e/d
                           (not-member-vars-lookup-when-not-member-find-key-with-var-bound-corollary
                            no-duplicate-keys-implies-find-key-with-var-bound
                            member-4v-sexpr-vars-list-hons-assoc-equal-impl-member-find-key-with-var-bound)
                           (sexpr-update-fixpoints
                            find-key-with-var-bound))
               :do-not-induct t)
              (and stable-under-simplificationp
                   '(:use ((:instance sexpr-deptable-ok-necc
                                      (sig (find-key-with-var-bound
                                            v (hons-shrink-alist
                                               (sexpr-update-fixpoints
                                                (hons-remove-duplicates (cdr (hons-assoc-equal signame deptable)))
                                                fixpoints
                                                (list (cons signame val)))
                                               (list (cons signame val)))))
                                      (var v)))))))))

(encapsulate
  nil
  (local
   (defthm 4v-sexpr-vars-4v-sexpr-restrict-with-rw-hons-shrink-alist
     (implies (and (not (member-equal k (4v-sexpr-vars-list
                                         (alist-vals (hons-shrink-alist al nil)))))
                   (not (and (member-equal k (4v-sexpr-vars x))
                             (not (member-equal k (alist-keys al))))))
              (not (member-equal k (4v-sexpr-vars (4v-sexpr-restrict-with-rw x al)))))
     :hints (("goal" :use ((:instance 4v-sexpr-vars-4v-sexpr-restrict-with-rw
                                      (al (hons-shrink-alist al nil))))
              :in-theory (disable 4v-sexpr-vars-4v-sexpr-restrict-with-rw)
              :do-not-induct t))))



  (local
   (defthm find-sexpr-least-fixpoint-member-need-fixing
     (b* (((mv fixpoints need-fixing &)
           (find-sexpr-least-fixpoint update-fns)))
       (implies (and (hons-assoc-equal v update-fns)
                     (member-equal v (4v-sexpr-vars-list
                                      (alist-vals
                                       (hons-shrink-alist fixpoints nil)))))
                (member-equal v need-fixing)))
     :hints (("goal" :induct t :do-not-induct t
              :in-theory (disable sexpr-update-fixpoints
                                  append default-car default-cdr
                                  4v-sexpr-restrict
                                  (:definition find-sexpr-least-fixpoint))
              :expand ((find-sexpr-least-fixpoint update-fns))))))


  (defthm find-sexpr-least-fixpoint-update-fn-sigs-in-need-fixing
    (b* (((mv & need-fixing &)
          (find-sexpr-least-fixpoint update-fns)))
      (implies (not (hons-assoc-equal v update-fns))
               (not (member-equal v need-fixing)))))

  (defthm find-sexpr-least-fixpoint-need-fixing-correct
    (b* (((mv fixpoints need-fixing &)
          (find-sexpr-least-fixpoint update-fns)))
      (implies (member-equal v (4v-sexpr-vars-list
                                (alist-vals
                                 (hons-shrink-alist fixpoints nil))))
               (iff (member-equal v need-fixing)
                    (hons-assoc-equal v update-fns))))))


(defthm need-fixing-subset-of-intersection
  (b* (((mv fixpoints need-fixing &)
          (find-sexpr-least-fixpoint update-fns)))
    (and (subsetp-equal need-fixing (alist-keys update-fns))
         (subsetp-equal (intersection-equal (4v-sexpr-vars-list
                                             (alist-vals
                                              (hons-shrink-alist fixpoints
                                                                 nil)))
                                            (alist-keys update-fns))
                        need-fixing)))
  :hints (("Goal" :do-not-induct t)
          (set-reasoning)))

(defthm-4v-sexpr-flag
  (defthm 4v-sexpr-restrict-when-keys-subset
    (implies (and (subsetp-equal keys full-keys)
                  (subsetp-equal (intersection-equal (4v-sexpr-vars x)
                                                     full-keys)
                                 keys))
             (equal (4v-sexpr-restrict x (hons-acons-each full-keys val nil))
                    (4v-sexpr-restrict x (hons-acons-each keys val nil))))
    :rule-classes nil
    :flag sexpr)
  (defthm 4v-sexpr-restrict-list-when-keys-subset
    (implies (and (subsetp-equal keys full-keys)
                  (subsetp-equal (intersection-equal (4v-sexpr-vars-list x)
                                                     full-keys)
                                 keys))
             (equal (4v-sexpr-restrict-list x (hons-acons-each full-keys val nil))
                    (4v-sexpr-restrict-list x (hons-acons-each keys val nil))))
    :rule-classes nil
    :flag sexpr-list)
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                           (alist-keys-member-hons-assoc-equal)))
          (witness :ruleset set-reasoning-no-consp)))

(defthm-4v-sexpr-flag
  (defthm 4v-sexpr-restrict-with-rw-when-keys-subset
    (implies (and (subsetp-equal keys full-keys)
                  (subsetp-equal (intersection-equal (4v-sexpr-vars x)
                                                     full-keys)
                                 keys))
             (equal (4v-sexpr-restrict-with-rw x (hons-acons-each full-keys val nil))
                    (4v-sexpr-restrict-with-rw x (hons-acons-each keys val nil))))
    :rule-classes nil
    :flag sexpr)
  (defthm 4v-sexpr-restrict-with-rw-list-when-keys-subset
    (implies (and (subsetp-equal keys full-keys)
                  (subsetp-equal (intersection-equal (4v-sexpr-vars-list x)
                                                     full-keys)
                                 keys))
             (equal (4v-sexpr-restrict-with-rw-list x (hons-acons-each full-keys val nil))
                    (4v-sexpr-restrict-with-rw-list x (hons-acons-each keys val nil))))
    :rule-classes nil
    :flag sexpr-list)
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                           (alist-keys-member-hons-assoc-equal)))
          (witness :ruleset set-reasoning-no-consp)))





(encapsulate
  nil
  (local (in-theory (e/d (alist-vals)
                         (4v-sexpr-restrict
                          default-car default-cdr
                          hons-acons-each
                          append not
                          member-when-atom
                          (:type-prescription subsetp-equal)
                          (:type-prescription member-equal)))))
  (defthm 4v-sexpr-restrict-alist-when-keys-subset
    (implies (and (subsetp-equal keys full-keys)
                  (subsetp-equal (intersection-equal (4v-sexpr-vars-list
                                                      (alist-vals x))
                                                     full-keys)
                                 keys))
             (alist-equiv
              (4v-sexpr-restrict-alist x (hons-acons-each full-keys val nil))
              (4v-sexpr-restrict-alist x (hons-acons-each keys val nil))))
    :hints (("goal" :induct (len x)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:use ((:instance 4v-sexpr-restrict-when-keys-subset
                                    (x (cdar x))))))
            (witness :ruleset set-reasoning-no-consp)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (alist-equiv-iff-agree-on-bad-guy)))))
    :rule-classes nil))

(defcong alist-equiv alist-equiv (4v-sexpr-restrict-alist a b) 1
  :hints (("goal" :in-theory (enable alist-equiv-when-agree-on-bad-guy))))

(defcong alist-equiv alist-equiv (4v-sexpr-restrict-with-rw-alist a b) 1
  :hints (("goal" :in-theory (enable alist-equiv-when-agree-on-bad-guy))))

(defthm 4v-sexpr-restrict-alist-when-keys-subset-corollary
    (implies (and (subsetp-equal keys full-keys)
                  (subsetp-equal (intersection-equal (4v-sexpr-vars-list
                                                      (alist-vals
                                                       (hons-shrink-alist x nil)))
                                                     full-keys)
                                 keys))
             (4v-sexpr-alist-equiv
              (4v-sexpr-restrict-alist x (hons-acons-each full-keys val nil))
              (4v-sexpr-restrict-alist x (hons-acons-each keys val nil))))
    :hints (("goal" :use ((:instance 4v-sexpr-restrict-alist-when-keys-subset
                                     (x (hons-shrink-alist x nil))))))
    :rule-classes nil)


(defthm 4v-sexpr-restrict-alist-atom
  (implies (atom a)
           (4v-sexpr-alist-equiv (4v-sexpr-restrict-alist x a) x))
  :hints (("goal"
           :in-theory (enable hons-assoc-equal)
           :induct t
           :do-not-induct t)
          (witness :ruleset 4v-sexpr-alist-equiv-witnessing)))

(defthm 4v-sexpr-fixpoint-spec-equiv-least-fixpoint-top
  (implies (no-duplicatesp-equal (alist-keys ups))
           (4v-sexpr-alist-equiv
            (find-sexpr-least-fixpoint-top ups)
            (4v-sexpr-fixpoint-spec ups)))
  :hints (("goal" :do-not-induct t
           :use ((:instance 4v-sexpr-restrict-alist-when-keys-subset-corollary
                            (x (mv-nth 0 (find-sexpr-least-fixpoint ups)))
                            (full-keys (alist-keys ups))
                            (keys (mv-nth 1 (find-sexpr-least-fixpoint ups)))
                            (val *4vx-sexpr*)))))
  :otf-flg t)

(defcong 4v-sexpr-alist-equiv iff (4v-sexpr-fixpoint-lower-boundp ups lb) 2
  :hints (("goal" :in-theory (disable 4v-sexpr-eval-alist))
          (witness :ruleset 4v-sexpr-fixpoint-lower-boundp-witnessing)
          (witness :ruleset 4v-sexpr-fixpoint-lower-boundp-eval-alist-ex)))


(defthm 4v-env-equiv-when-4v-alist-<=-both-ways
  (implies (and (4v-alist-<= a b)
                (4v-alist-<= b a))
           (equal (4v-env-equiv a b) t))
  :hints (("goal" :in-theory (disable 4v-fix))
          (witness :ruleset 4v-env-equiv-witnessing)
          (witness :ruleset 4v-alist-<=-hons-assoc-equal-example)))


(defthm 4v-sexpr-least-fixpoint-unique
  (implies (and (4v-sexpr-fixpoint-lower-boundp update-fns lb1)
                (4v-sexpr-fixpoint-lower-boundp update-fns lb2)
                (4v-sexpr-fixpointp update-fns lb1)
                (4v-sexpr-fixpointp update-fns lb2)
                (keys-equiv lb1 update-fns)
                (keys-equiv lb2 update-fns))
           (4v-sexpr-alist-equiv lb1 lb2))
  :rule-classes nil
  :hints (("goal" :in-theory (e/d (4v-sexpr-alist-equiv-is-alt)
                                  (4v-env-equiv-to-key-and-env-equiv
                                   4v-sexpr-eval-alist)))
          (witness :ruleset 4v-sexpr-alist-equiv-alt-witnessing)
          (witness :ruleset 4v-sexpr-alist-equiv-alt-eval-alist-ex)
          (and stable-under-simplificationp
               '(:use ((:instance 4v-sexpr-fixpoint-lower-boundp-necc
                                  (ups update-fns)
                                  (lb lb1)
                                  (fp (4v-sexpr-eval-alist lb2 env0))
                                  (env env0))
                       (:instance 4v-sexpr-fixpoint-lower-boundp-necc
                                  (ups update-fns)
                                  (lb lb2)
                                  (fp (4v-sexpr-eval-alist lb1 env0))
                                  (env env0)))))))

(in-theory (disable 4v-sexpr-fixpoint-spec-equiv-without-xes))

(defcong 4v-sexpr-alist-equiv iff (4v-sexpr-fixpointp ups fixpoint) 1
  :hints(("goal":do-not-induct t)
         (witness :ruleset 4v-sexpr-fixpointp-witnessing)
         (witness :ruleset 4v-sexpr-fixpointp-hons-assoc-equal-ex)))



(defthm fixpoint-spec-of-equiv-update-fns
  (implies (and (no-duplicatesp-equal (alist-keys ups))
                (no-duplicatesp-equal (alist-keys ups-equiv))
                (4v-sexpr-alist-equiv (double-rewrite ups)
                                      (double-rewrite ups-equiv)))
           (equal (4v-sexpr-alist-equiv (4v-sexpr-fixpoint-spec ups)
                                        (4v-sexpr-fixpoint-spec ups-equiv))
                  t))
  :hints (("goal" :use ((:instance 4v-sexpr-least-fixpoint-unique
                                   (update-fns ups)
                                   (lb1 (4v-sexpr-fixpoint-spec ups))
                                   (lb2 (4v-sexpr-fixpoint-spec ups-equiv)))
                        (:instance
                         4v-sexpr-fixpoint-lower-boundp-4v-sexpr-fixpoint-spec
                         (update-fns ups-equiv))
                        (:instance
                         4v-sexpr-fixpointp-4v-sexpr-fixpoint-spec
                         (ups ups-equiv)))
           :in-theory (disable 4v-sexpr-fixpointp-is-alt1)
           :do-not-induct t)))




(defthm not-hons-assoc-equal-impl-not-member-collect-keys
  (implies (not (hons-assoc-equal key al))
           (not (member-equal key (collect-keys-with-value al val)))))


(defthm sexpr-dfs-not-finished-when-present
  (implies (and (not (member-equal key (collect-keys-with-value seen-al
                                                                'finished)))
                (hons-get key seen-al))
           (not (member-equal
                 key
                 (collect-keys-with-value
                  (mv-nth
                   0 (sexpr-dfs queue deps seen-al
                               parent back-edges))
                  'finished))))
  :hints(("Goal" :in-theory
          (e/d ()
               (4v-sexpr-vars default-car default-cdr
                           union-equal member-when-atom
                           subsetp-car-member
                           alist-keys-when-atom)))))

(defthm no-duplicatesp-sexpr-dfs-finished
  (implies (no-duplicatesp-equal
            (collect-keys-with-value seen-al 'finished))
           (no-duplicatesp-equal
            (collect-keys-with-value
             (mv-nth 0 (sexpr-dfs queue deps seen-al parent
                                 back-edges))
             'finished)))
  :hints (("goal" :induct (sexpr-dfs queue deps seen-al parent
                                 back-edges)
           :in-theory (disable default-car member-of-cons union-equal
                               default-cdr 4v-sexpr-vars)
           :do-not-induct t)))


(defthm sexpr-dfs-finished-before-started
  (implies (member-equal x (collect-keys-with-value
                            seen-al 'finished))
           (member-equal
            x (collect-keys-with-value
               (mv-nth 0 (sexpr-dfs queue deps seen-al parent
                                   back-edges))
               'finished)))
  :hints (("goal" :induct (sexpr-dfs queue deps seen-al parent
                                 back-edges)
           :in-theory (disable default-car union-equal
                               default-cdr)
           :do-not-induct t)))


(defthm sexpr-dfs-finished-if-present
  (let ((res (mv-nth 0 (sexpr-dfs queue deps seen-al
                                 parent back-edges))))
    (implies (and (not (hons-assoc-equal x seen-al))
                  (hons-assoc-equal x res))
             (member-equal x (collect-keys-with-value res 'finished))))
  :hints (("goal" :induct (sexpr-dfs queue deps seen-al parent
                                 back-edges)
           :in-theory (disable default-car union-equal
                               default-cdr 4v-sexpr-vars
                               sexpr-hons-assoc-equal-in-seen-al
                               (:definition sexpr-dfs))
           :expand (sexpr-dfs queue deps seen-al parent
                                 back-edges)
           :do-not-induct t)))



(defthm sexpr-dfs-all-in-queue-finished
  (implies (and (member-equal x queue)
                (hons-assoc-equal x deps)
                (implies (hons-assoc-equal x seen-al)
                         (member-equal x (collect-keys-with-value
                                          seen-al 'finished))))
           (member-equal
            x (collect-keys-with-value
               (mv-nth 0 (sexpr-dfs queue deps seen-al parent
                                   back-edges))
               'finished)))
  :hints (("goal" :induct (sexpr-dfs queue deps seen-al parent
                                 back-edges)
           :expand ((sexpr-dfs queue deps seen-al parent
                              back-edges))
           :in-theory (disable
                       (:definition sexpr-dfs)
                       default-car  union-equal
                       sexpr-dfs-not-finished-when-present
                       subsetp-when-atom-left
                       not-hons-assoc-equal-impl-not-member-collect-keys
                       aig-vars
                       default-cdr)
           :do-not-induct t)))


(defthm sexpr-dfs-all-in-queue-finished-when-empty
  (implies (subsetp-equal queue (alist-keys deps))
           (subsetp-equal
            queue
            (collect-keys-with-value
             (mv-nth 0 (sexpr-dfs queue deps nil parent back-edges))
             'finished)))
  :hints (("goal" :do-not-induct t
           :in-theory (disable sexpr-dfs))
          (set-reasoning)))


(defthm sexpr-dfs-finished-implies-update-fn
  (implies (and (not (hons-assoc-equal x deps))
                (not (hons-assoc-equal x seen-al)))
           (not (hons-assoc-equal
                 x (mv-nth 0 (sexpr-dfs queue deps seen-al
                                       parent back-edges)))))
  :hints (("goal" :do-not-induct t
           :induct (sexpr-dfs queue deps seen-al parent
                             back-edges))))


(defthm sexpr-dfs-subset-of-deps
  (subsetp-equal (collect-keys-with-value
                  (mv-nth 0 (sexpr-dfs queue deps nil
                                       parent back-edges))
                  'finished)
                 (alist-keys deps))

  :hints (("goal" :do-not-induct t
           :in-theory (disable sexpr-dfs))
          (set-reasoning)))



(encapsulate nil
  (local (defthm set-equiv-finished-of-sexpr-dfs1
           (implies (equal (alist-keys deps) (alist-keys update-fns))
                    (set-equiv (collect-keys-with-value
                                 (mv-nth 0 (sexpr-dfs (alist-keys update-fns)
                                                      deps nil parent
                                                      back-edges))
                                 'finished)
                                (alist-keys update-fns)))
           :hints(("Goal" :in-theory (enable set-equiv)))))

  (local (defthm alist-keys-sexpr-update-fns-to-deps
           (equal (alist-keys (sexpr-update-fns-to-deps update-fns))
                  (alist-keys update-fns))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defthm set-equiv-finished-of-sexpr-dfs
    (set-equiv (collect-keys-with-value
                 (mv-nth 0 (sexpr-dfs (alist-keys update-fns)
                                      (sexpr-update-fns-to-deps update-fns)
                                      nil parent back-edges))
                 'finished)
                (alist-keys update-fns)))

  (defthm member-equal-finished-of-sexpr-dfs
    (iff (member-equal x  (collect-keys-with-value
                           (mv-nth 0 (sexpr-dfs (alist-keys update-fns)
                                                (sexpr-update-fns-to-deps update-fns)
                                                nil parent back-edges))
                           'finished))
         (member-equal x (alist-keys update-fns)))))



(in-theory (disable sexpr-dfs))


(defthm alist-equiv-fal-extract
  (implies (set-equiv keys (alist-keys al))
           (alist-equiv (fal-extract keys al)
                        al))
  :hints (("goal" :do-not-induct t)
          (witness :ruleset alist-equiv-witnessing)
          (set-reasoning))
  :otf-flg t)


(defthm alist-keys-fal-extract-when-subset-of-alist-keys
  (implies (and (subsetp-equal (double-rewrite keys)
                               (double-rewrite (alist-keys al)))
                (true-listp keys))
           (equal (alist-keys (fal-extract keys al))
                  (double-rewrite keys)))
  :hints(("Goal" :in-theory (enable subsetp-equal fal-extract
                                    (:type-prescription hons-assoc-equal)))))


(defthm sexpr-fixpoints-impl-matches-spec
  (4v-sexpr-alist-equiv (sexpr-fixpoints update-fns)
                        (4v-sexpr-fixpoint-spec (hons-shrink-alist update-fns nil)))
  :hints (("goal" :do-not-induct t
           :in-theory (disable sexpr-dfs
                               reverse
                               find-sexpr-least-fixpoint-top))))

(in-theory (disable sexpr-fixpoints))

(defthm 4v-sexpr-fixpointp-4v-sexpr-fixpoint-spec-rw
  (implies (and (4v-sexpr-alist-equiv (double-rewrite ups)
                                      (double-rewrite in-ups))
                (no-duplicatesp-equal (alist-keys in-ups)))
           (4v-sexpr-fixpointp ups (4v-sexpr-fixpoint-spec in-ups)))
  :hints (("goal" :use ((:instance 4v-sexpr-fixpointp-4v-sexpr-fixpoint-spec
                                   (ups in-ups)))
           :in-theory (disable 4v-sexpr-fixpointp-4v-sexpr-fixpoint-spec))))

(defthm 4v-sexpr-fixpoint-lower-boundp-4v-sexpr-fixpoint-spec-rw
  (implies (and (4v-sexpr-alist-equiv (double-rewrite ups)
                                      (double-rewrite in-ups))
                (no-duplicatesp-equal (alist-keys in-ups)))
           (4v-sexpr-fixpoint-lower-boundp ups (4v-sexpr-fixpoint-spec in-ups)))
  :hints (("goal" :use
           ((:instance
             4v-sexpr-fixpoint-lower-boundp-4v-sexpr-fixpoint-spec
             (update-fns in-ups)))
           :in-theory
           (disable 4v-sexpr-fixpoint-lower-boundp-4v-sexpr-fixpoint-spec))))


(defthm 4v-sexpr-fixpointp-sexpr-fixpoints
  (4v-sexpr-fixpointp ups (sexpr-fixpoints ups)))

(defthm 4v-sexpr-fixpoint-lower-boundp-sexpr-fixpoints
  (4v-sexpr-fixpoint-lower-boundp ups (sexpr-fixpoints ups)))


(defthm vars-of-4v-sexpr-restrict-alist
  (implies (and (not (member-equal v (4v-sexpr-vars-list (alist-vals env))))
                (or (not (member-equal v (4v-sexpr-vars-list (alist-vals al))))
                    (member-equal v (alist-keys env))))
           (not (member-equal v (4v-sexpr-vars-list (alist-vals
                                                  (4v-sexpr-restrict-alist al
                                                                        env)))))))

(defthm vars-of-4v-sexpr-restrict-with-rw-alist
  (implies (and (not (member-equal v (4v-sexpr-vars-list (alist-vals env))))
                (or (not (member-equal v (4v-sexpr-vars-list (alist-vals al))))
                    (member-equal v (alist-keys env))))
           (not (member-equal v (4v-sexpr-vars-list
                                 (alist-vals
                                  (4v-sexpr-restrict-with-rw-alist al env)))))))

(defthm 4v-sexpr-vars-list-alist-vals-hons-acons-each
  (implies (and (not (member-equal v (4v-sexpr-vars val)))
                (not (member-equal v (4v-sexpr-vars-list (alist-vals acc)))))
           (not (member-equal v (4v-sexpr-vars-list (alist-vals (hons-acons-each
                                                              keys val
                                                              acc))))))
  :hints(("Goal" :in-theory (enable hons-acons-each))))


(defthm find-sexpr-least-fixpoint-need-fixing-correct-lemma
    (b* (((mv fixpoints need-fixing &)
          (find-sexpr-least-fixpoint update-fns)))
      (implies (and (not (member-equal v (double-rewrite need-fixing)))
                    (hons-assoc-equal v (double-rewrite update-fns)))
               (not (member-equal v (4v-sexpr-vars-list
                                     (alist-vals
                                      (hons-shrink-alist fixpoints nil))))))))

(defthm keys-not-present-in-fixpoint-vars
  (implies (member-equal x (alist-keys update-fns))
           (not (member-equal
                 x (4v-sexpr-vars-list
                    (alist-vals (sexpr-fixpoints update-fns))))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (sexpr-fixpoints)
                           (find-sexpr-least-fixpoint
                            append-of-nil))))
  :otf-flg t)

(defthm not-member-vars-of-hons-shrink-alist-when-not-member-vars-alist
  (implies (and (not (member-equal v (4v-sexpr-vars-list (alist-vals al))))
                (not (member-equal v (4v-sexpr-vars-list (alist-vals acc)))))
           (not (member-equal v (4v-sexpr-vars-list (alist-vals
                                                  (hons-shrink-alist al acc)))))))


(defthm vars-of-sexpr-update-fixpoints-are-vars-of-fixpoints-and-new-fixpoint
  (implies (and (not (member-equal v (4v-sexpr-vars-list (alist-vals fixpoints))))
                (not (member-equal v (4v-sexpr-vars-list (alist-vals
                                                       new-fixpoint)))))
           (not (member-equal v (4v-sexpr-vars-list
                                 (alist-vals
                                  (sexpr-update-fixpoints
                                   deps fixpoints new-fixpoint)))))))

(defthm find-sexpr-least-fixpoint-vars-are-vars-of-update-fns
  (implies (not (member-equal x (4v-sexpr-vars-list (alist-vals update-fns))))
           (not (member-equal x (4v-sexpr-vars-list
                                 (alist-vals
                                  (mv-nth 0 (find-sexpr-least-fixpoint
                                             update-fns)))))))
  :hints(("Goal" :in-theory (disable hons-assoc-equal
                                     sexpr-update-fixpoints
                                     4v-sexpr-restrict
                                     find-sexpr-least-fixpoint)
          :expand (find-sexpr-least-fixpoint update-fns)
          :induct (len update-fns))))

(defthm vars-of-fal-extract-are-vars-of-update-fns
  (implies (not (member-equal x (4v-sexpr-vars-list (alist-vals update-fns))))
           (not (member-equal x (4v-sexpr-vars-list
                                 (alist-vals
                                  (fal-extract keys update-fns))))))
  :hints(("Goal" :in-theory (enable fal-extract))))

(defthm fixpoint-vars-are-vars-of-update-fns
  (implies (not (member-equal x (4v-sexpr-vars-list (alist-vals update-fns))))
           (not (member-equal x (4v-sexpr-vars-list
                                 (alist-vals (sexpr-fixpoints update-fns))))))
  :hints(("Goal" :in-theory (e/d (Sexpr-fixpoints)
                                 (find-sexpr-least-fixpoint))
          :do-not-induct t))
  :otf-flg t)

(defthm keys-of-sexpr-fixpoints
  (iff (hons-assoc-equal x (sexpr-fixpoints update-fns))
       (hons-assoc-equal x update-fns)))











;;=========================================

;; Proof that sexpr-fixpoint-with-varmap works.









(defthm-4v-sexpr-flag
  (defthm 4v-sexpr-eval-4v-sexpr-compose
    (equal (4v-sexpr-eval (4v-sexpr-compose x al) env)
           (4v-sexpr-eval x (4v-sexpr-eval-alist al env)))
    :flag sexpr)
  (defthm 4v-sexpr-eval-list-4v-sexpr-compose-list
    (equal (4v-sexpr-eval-list (4v-sexpr-compose-list x al) env)
           (4v-sexpr-eval-list x (4v-sexpr-eval-alist al env)))
    :flag sexpr-list)
  :hints (("goal" :in-theory (disable* (:ruleset 4v-op-defs)
                                       4v-sexpr-eval-alist))))

(defthm 4v-sexpr-eval-alist-4v-sexpr-compose-alist
  (equal (4v-sexpr-eval-alist (4v-sexpr-compose-alist x al) env)
         (4v-sexpr-eval-alist x (4v-sexpr-eval-alist al env)))
  :hints(("Goal" :in-theory (disable 4v-sexpr-eval))))



(defthm 4v-sexpr-eval-alist-translate-domain
  (equal (4v-sexpr-eval-alist (translate-domain al map) env)
         (translate-domain (4v-sexpr-eval-alist al env) map)))




(defexample keys-equiv-hons-assoc-equal-ex
  :pattern (hons-assoc-equal k al)
  :templates (k)
  :instance-rulename keys-equiv-instancing)




(defthm keys-equiv-sexpr-fixpoints
  (keys-equiv (sexpr-fixpoints ups)
              ups)
  :hints(("goal" :in-theory (disable sexpr-fixpoints))
         (witness :ruleset keys-equiv-witnessing)))


(defthm hons-assoc-equal-translate-domain
  (implies (unique-mapping map)
           (equal (hons-assoc-equal x (translate-domain al map))
                  (and (hons-rassoc-equal x map)
                       (hons-assoc-equal (car (hons-rassoc-equal x map)) al)
                       (cons x (cdr (hons-assoc-equal (car (hons-rassoc-equal x map)) al))))))
  :hints (("goal" :induct (len al))))

(encapsulate nil
  (local
   (progn
     (defun lookup-from-translated-domain (k al map)
       (if (atom al)
           nil
         (if (and (consp (car al))
                  (hons-assoc-equal (caar al) map)
                  (equal k (cdr (hons-assoc-equal (caar al) map))))
             (car al)
           (lookup-from-translated-domain k (cdr al) map))))


     (defthm lookup-from-translated-domain-when-key
       (implies (and (equal (cdr (hons-assoc-equal k map)) x)
                     (hons-assoc-equal k map)
                     (hons-assoc-equal k al))
                (lookup-from-translated-domain x al map)))

     (defthm hons-assoc-equal-translate-domain2
       (equal (hons-assoc-equal x (translate-domain al map))
              (and (lookup-from-translated-domain x al map)
                   (cons x (cdr (lookup-from-translated-domain x al map))))))

     (defun find-not-lookup-term (x)
       (if (atom x)
           nil
         (let ((term (car x)))
           (case-match term
             (('not ('lookup-from-translated-domain . &) . &)
              (car x))
             (& (find-not-lookup-term (cdr x)))))))

     (defthm hons-assoc-equal-of-car-lookup-from-translated
       (implies (lookup-from-translated-domain x al map)
                (and (hons-assoc-equal
                      (car (lookup-from-translated-domain x al map))
                      al)
                     (hons-assoc-equal
                      (car (lookup-from-translated-domain x al map))
                      map)
                     (equal (cdr (hons-assoc-equal
                                  (car (lookup-from-translated-domain x al map))
                                  map))
                            x)))
       :hints (("goal" :induct (len al))))


     (defcong keys-equiv iff (lookup-from-translated-domain x al map) 2
       :hints (("goal" :do-not-induct t
                :in-theory (disable lookup-from-translated-domain-when-key))
               (and stable-under-simplificationp
                    (let ((look-term (assoc 'lookup-from-translated-domain clause))
                          (not-look-term (cadr (find-not-lookup-term clause))))
                      `(:use ((:instance lookup-from-translated-domain-when-key
                                         (k (car ,not-look-term))
                                         (x ,(cadr look-term))
                                         (al ,(caddr look-term))
                                         (map ,(cadddr look-term)))))))
               (witness :ruleset keys-equiv-hons-assoc-equal-ex))
       :otf-flg t)))



  (defcong keys-equiv keys-equiv (translate-domain al map) 1
    :hints (("goal" :do-not-induct t)
            (witness :ruleset keys-equiv-witnessing))))






(defcong keys-equiv keys-equiv (4v-sexpr-compose-alist al env) 1
  :hints ((witness :ruleset keys-equiv-witnessing)))





(defthm 4v-sexpr-list-equiv-nil-x
  (implies (not (consp x))
           (equal (4v-sexpr-list-equiv nil x) t))
  :hints (("goal" :do-not-induct t)
          (witness :ruleset 4v-sexpr-list-equiv-witnessing)))

(defthm 4v-sexpr-eval-lookup-in-atom-val-alist
  (implies (sexpr-var-val-alistp al)
           (equal (4v-sexpr-eval (cdr (hons-assoc-equal x al)) env)
                  (if (hons-assoc-equal x al)
                      (4v-lookup (cdr (hons-assoc-equal x al)) env)
                    *4vx*))))

(defthm hons-assoc-equal-reverse-alist
  (equal (hons-assoc-equal x (reverse-alist al))
         (and (hons-rassoc-equal x al)
              (cons x (car (hons-rassoc-equal x al)))))
  :hints(("Goal" :in-theory (enable hons-rassoc-equal))))


(defthm-4v-sexpr-flag
  (defthm 4v-sexpr-compose-reverse-unique-map
    (implies (and (sexpr-var-val-alistp al)
                  (unique-mapping al)
                  (subsetp-equal (4v-sexpr-vars x)
                                 (alist-keys al)))
             (4v-sexpr-equiv (4v-sexpr-compose (4v-sexpr-compose x al)
                                            (reverse-alist al))
                             x))
    :flag sexpr)
  (defthm 4v-sexpr-compose-list-reverse-unique-map
    (implies (and (sexpr-var-val-alistp al)
                  (unique-mapping al)
                  (subsetp-equal (4v-sexpr-vars-list x)
                                 (alist-keys al)))
             (4v-sexpr-list-equiv
              (4v-sexpr-compose-list (4v-sexpr-compose-list x al)
                                  (reverse-alist al))
              x))
    :flag sexpr-list)
  :hints (("goal" :in-theory (e/d (subsetp-equal)
                                  (4v-fix)))
          (witness :ruleset 4v-sexpr-equiv-witnessing)))

(defthm-4v-sexpr-flag
  (defthm 4v-sexpr-compose-reverse-unique-map
    (implies (and (sexpr-var-val-alistp al)
                  (unique-mapping al)
                  (subsetp-equal (4v-sexpr-vars x)
                                 (alist-keys al)))
             (4v-sexpr-equiv (4v-sexpr-compose (4v-sexpr-compose x al)
                                            (reverse-alist al))
                             x))
    :flag sexpr)
  (defthm 4v-sexpr-compose-list-reverse-unique-map
    (implies (and (sexpr-var-val-alistp al)
                  (unique-mapping al)
                  (subsetp-equal (4v-sexpr-vars-list x)
                                 (alist-keys al)))
             (4v-sexpr-list-equiv
              (4v-sexpr-compose-list (4v-sexpr-compose-list x al)
                                  (reverse-alist al))
              x))
    :flag sexpr-list)
  :hints (("goal" :in-theory (e/d (subsetp-equal)
                                  (4v-fix)))
          (witness :ruleset 4v-sexpr-equiv-witnessing)))

(defthm sexpr-alist-equiv-nil
  (implies (not (consp x))
           (equal (4v-sexpr-alist-equiv nil x) t))
  :hints ((witness :ruleset 4v-sexpr-alist-equiv-witnessing)))

(defthm sexpr-alist-equiv-atom-car
  (implies (not (consp (car x)))
           (equal (4v-sexpr-alist-equiv (cdr x) x) t))
  :hints (("Goal" :in-theory (enable hons-assoc-equal))
          (witness :ruleset 4v-sexpr-alist-equiv-witnessing)))

(defthm 4v-sexpr-compose-alist-reverse-unique-map
  (implies (and (sexpr-var-val-alistp map)
                (unique-mapping map)
                (subsetp-equal (4v-sexpr-vars-list (alist-vals x))
                               (alist-keys map)))
           (4v-sexpr-alist-equiv (4v-sexpr-compose-alist
                                  (4v-sexpr-compose-alist x map)
                                  (reverse-alist map))
                                 x)))

(defthm alist-equiv-cdr-x-when-not-consp-car
  (implies (not (consp (car x)))
           (alist-equiv (cdr x) x))
  :hints(("Goal" :in-theory (enable alist-equiv-iff-agree-on-bad-guy))))

(defthm alist-equiv-nil-when-not-consp
  (implies (not (consp x))
           (equal (alist-equiv nil x) t))
  :hints(("Goal" :in-theory (enable alist-equiv-iff-agree-on-bad-guy))))


(defthm translate-domain-cancel
  (implies (and (unique-mapping map)
                (subsetp-equal (alist-keys (double-rewrite x))
                               (alist-keys (double-rewrite map))))
           (alist-equiv (translate-domain (translate-domain x map)
                                          (reverse-alist map))
                        x))
  :hints(("Goal" :in-theory (enable alist-keys subsetp-equal))))

(defthm keys-equiv-4v-sexpr-compose-alist
  (keys-equiv (4v-sexpr-compose-alist al env)
              (double-rewrite al))
  :hints ((witness :ruleset keys-equiv-witnessing)))


(defthm alist-keys-reverse-alist
  (equal (alist-keys (reverse-alist al))
         (alist-vals al)))

(defthm alist-vals-reverse-alist
  (equal (alist-vals (reverse-alist al))
         (alist-keys al)))

(defthmd hons-rassoc-equal-iff-member-alist-vals
  ;; bozo also in aig/decomp
  (iff (hons-rassoc-equal x al)
       (member-equal x (alist-vals al))))

(defthm hons-rassoc-equal-in-reverse-alist
  (implies (no-duplicatesp-equal (alist-keys map))
           (equal (hons-rassoc-equal key (reverse-alist map))
                  (and (hons-assoc-equal key map)
                       (cons (cdr (hons-assoc-equal key map))
                             key)))))

(defthm keys-equiv-translate-domain-lemma
  (implies (and (keys-equiv (translate-domain x map) y)
                (unique-mapping map)
                (subsetp-equal (alist-keys (double-rewrite x))
                               (alist-keys (double-rewrite map))))
           (keys-equiv (translate-domain y (reverse-alist map))
                       x))
  :hints (("goal" :do-not-induct t)))

(defthm no-duplicate-vals-lookups-equal
  (implies (and (no-duplicatesp-equal (alist-vals map))
                (hons-assoc-equal k map)
                (hons-assoc-equal j map))
           (equal (equal (cdr (hons-assoc-equal k map))
                         (cdr (hons-assoc-equal j map)))
                  (equal k j)))
  :hints(("Goal" :in-theory (enable hons-assoc-equal))))

;; (defthm lookup-from-translated-domain-when-key-with-unique-map
;;   (implies (and (equal (cdr (hons-assoc-equal k map)) x)
;;                 (hons-assoc-equal k map)
;;                 (hons-assoc-equal k al)
;;                 (unique-mapping map))
;;            (equal (lookup-from-translated-domain x al map)
;;                   (hons-assoc-equal k al))))

;; (defthm cdr-lookup-from-translated-domain
;;   (implies (lookup-from-translated-domain x al map)
;;            (equal (cdr (lookup-from-translated-domain x al map))
;;                   (cdr (hons-assoc-equal
;;                         (car (lookup-from-translated-domain x al map))
;;                         al)))))


;; (defthm not-hons-assoc-equal-car-lookup-from-translated
;;   (implies (not (hons-assoc-equal (car (lookup-from-translated-domain x a map))
;;                                   a))
;;            (equal (lookup-from-translated-domain x a map)
;;                   nil)))

;; (defthm 4v-env-equiv-implies-4v-cdr-equiv-lookup-from-translated-domain
;;   (implies (and (4v-env-equiv a b)
;;                 (unique-mapping map))
;;            (equal (4v-cdr-equiv (lookup-from-translated-domain x a map)
;;                                 (lookup-from-translated-domain x b map))
;;                   t))
;;   :hints (("goal" :do-not-induct t
;;            :in-theory (disable 4v-fix)
;;            :use ((:instance 4v-env-equiv-necc
;;                             (x a) (y b)
;;                             (key (car (lookup-from-translated-domain x a
;;                                                                      map))))
;;                  (:instance 4v-env-equiv-necc
;;                             (x a) (y b)
;;                             (key (car (lookup-from-translated-domain x b map)))))))
;;   :otf-flg t)



;; (defcong 4v-env-equiv 4v-cdr-equiv
;;   (lookup-from-translated-domain
;;    x al map) 2
;;    :hints(("Goal" :in-theory
;;            (e/d ()
;;                 (4v-cdr-equiv
;;                  4v-env-equiv-to-key-and-env-equiv))
;;            :do-not-induct t))
;;    :otf-flg t)

;; (defcong 4v-env-equiv 4v-env-equiv (translate-domain x map) 1
;;   :hints (("goal" :do-not-induct t
;;            :in-theory (disable 4v-fix))
;;           (witness :ruleset 4v-env-equiv-witnessing)
;;           (and stable-under-simplificationp
;;                '(:use ((:instance 4v-env-equiv-necc
;;                                   (y x-equiv)
;;                                   (key (car (lookup-from-translated-domain
;;                                              key0 x map))))
;;                        (:instance 4v-env-equiv-necc
;;                                   (y x-equiv)
;;                                   (key (car (lookup-from-translated-domain
;;                                              key0 x-equiv map))))))))
;;   :otf-flg t)



(defthm 4v-env-equiv-translate-domain-lemma
  (implies (and (4v-env-equiv (translate-domain x map) y)
                (unique-mapping map)
                (subsetp-equal (alist-keys (double-rewrite x))
                               (alist-keys (double-rewrite map))))
           (4v-env-equiv (translate-domain y (reverse-alist map))
                         x))
  :hints (("goal" :do-not-induct t
           :in-theory (disable 4v-fix no-duplicatesp-equal
                               hons-assoc-equal))
          (witness :ruleset 4v-env-equiv-witnessing)
          (and stable-under-simplificationp
               '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                 (4v-fix alist-keys-member-hons-assoc-equal
                                         hons-assoc-equal
                                         no-duplicatesp-equal))))
          (witness :ruleset set-reasoning-no-consp)
          (and stable-under-simplificationp
               '(:in-theory (disable 4v-fix hons-assoc-equal
                                     no-duplicatesp-equal)))
          (witness :ruleset 4v-env-equiv-hons-assoc-equal-ex))
  :otf-flg t)





;; BOZO these are good rules but they're screwing up the normal form that
;; was being used here, will have to update the thms above to match
(local (in-theory (disable commutativity-of-append-under-set-equiv
                           SET-EQUIV-WITH-APPEND-OTHER-LEFT)))

(defthm 4v-sexpr-equiv-append-translate-domain
  (implies (and (keys-equiv (translate-domain ups map)
                            fp0)
                (subsetp-equal (alist-keys ups)
                               (alist-keys map))
                (sexpr-var-val-alistp map)
                (unique-mapping map))
           (4v-env-equiv (append (Translate-domain fp0 (reverse-alist map))
                                 (4v-sexpr-eval-alist map env0))
                         (4v-sexpr-eval-alist map (append fp0 env0))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable 4v-fix))
          (witness :ruleset 4v-env-equiv-witnessing)))

(defthm 4v-alist-<=-translate-domain
  (implies (and (unique-mapping map)
                (4v-alist-<= a b))
           (4v-alist-<= (translate-domain a map)
                        (translate-domain b map)))
  :hints (("goal" :do-not-induct t
           :in-theory (disable 4v-fix))
          (witness :ruleset 4v-alist-<=-witnessing)
          (and stable-under-simplificationp
               '(:use ((:instance 4v-alist-<=-necc
                                  (x a) (y b)
                                  (k (car (hons-rassoc-equal k0 map)))))))))


(defthm 4v-alist-<=-translate-domain-reverse1
  (implies (unique-mapping map)
           (implies (not (4v-alist-<= (translate-domain a map) b))
                    (not (4v-alist-<= a (translate-domain b (reverse-alist map))))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable 4v-fix))
          (witness :ruleset 4v-alist-<=-witnessing)
          (and stable-under-simplificationp
               '(:use ((:instance 4v-alist-<=-necc
                                  (x a)
                                  (y (translate-domain b (reverse-alist map)))
                                  (k (car (hons-rassoc-equal k0 map))))))))
  :otf-flg t)

(defthm 4v-alist-<=-translate-domain-reverse2
  (implies (and (unique-mapping map)
                (subsetp-equal (alist-keys a) (alist-keys map)))
           (implies (4v-alist-<= (translate-domain a map) b)
                    (4v-alist-<= a (translate-domain b (reverse-alist map)))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d* (hons-assoc-equal-iff-member-alist-keys)
                            ((:rules-of-class :type-prescription :here)
                             4v-fix alist-keys-member-hons-assoc-equal
                             hons-assoc-equal default-car default-cdr
                             translate-domain
                             no-duplicatesp-equal)))
          (witness :ruleset 4v-alist-<=-witnessing)
          (witness :ruleset set-reasoning-member-template)
          (and stable-under-simplificationp
               '(:use ((:instance 4v-alist-<=-necc
                                  (x (translate-domain a map))
                                  (y b)
                                  (k (cdr (hons-assoc-equal k0 map))))))))
  :otf-flg t)



(defthm 4v-alist-<=-translate-domain-lemma
  (implies (and (4v-env-equiv (translate-domain b map)
                              c)
                (4v-alist-<= a b)
                (unique-mapping map))
           (4v-alist-<= (translate-domain a map) c)))

(defthm 4v-sexpr-fixpoint-lower-boundp-translate-domain
  (implies (and (unique-mapping map)
                (subsetp-equal (alist-keys ups) (alist-keys map))
                (4v-sexpr-fixpoint-lower-boundp ups lb)
                (sexpr-var-val-alistp map))
           (4v-sexpr-fixpoint-lower-boundp
            (translate-domain (4v-sexpr-compose-alist ups map) map)
            (translate-domain (4v-sexpr-compose-alist lb map) map)))
  :hints (("goal" :do-not-induct t
           :in-theory (disable 4v-env-equiv-to-key-and-env-equiv))
          (witness :ruleset 4v-sexpr-fixpoint-lower-boundp-witnessing)
          (and stable-under-simplificationp
               '(:use ((:instance 4v-sexpr-fixpoint-lower-boundp-necc
                                  (fp (translate-domain fp0
                                                        (reverse-alist map)))
                                  (env (4v-sexpr-eval-alist map env0)))))))
  :otf-flg t)



;; ;;;;  NOTE: The next few are redundant with theorems in sexpr-fixpoint-spec.
;; (defthm hons-assoc-equal-4v-sexpr-restrict-alist
;;   (equal (hons-assoc-equal k (4v-sexpr-restrict-alist x al))
;;          (and (hons-assoc-equal k x)
;;               (double-rewrite
;;                (cons k (4v-sexpr-restrict (cdr (hons-assoc-equal k x)) al))))))

;; (defexample 4v-sexpr-fixpointp-hons-assoc-equal-ex
;;   :pattern (hons-assoc-equal k ups)
;;   :templates (k)
;;   :instance-rulename 4v-sexpr-fixpointp-instancing)

;; (defthmd 4v-sexpr-alist-equiv-fixpoint
;;   (implies (and (4v-sexpr-fixpointp ups fixpoint)
;;                 (keys-equiv ups fixpoint))
;;            (4v-sexpr-alist-equiv (4v-sexpr-restrict-alist ups fixpoint)
;;                                  fixpoint))
;;   :hints ((witness :ruleset
;;                    (4v-sexpr-alist-equiv-witnessing
;;                     4v-sexpr-fixpointp-hons-assoc-equal-ex))))

;; (defthmd 4v-sexpr-fixpointp-is-alt
;;   (implies (keys-equiv (double-rewrite ups)
;;                        (double-rewrite fixpoint))
;;            (iff (4v-sexpr-fixpointp ups fixpoint)
;;                 (4v-sexpr-alist-equiv (4v-sexpr-restrict-alist ups fixpoint)
;;                                       fixpoint)))
;;   :hints(("Goal" :in-theory (enable 4v-sexpr-alist-equiv-fixpoint)
;;           :do-not-induct t)
;;          (witness :ruleset (4v-sexpr-fixpointp-witnessing
;;                             4v-sexpr-alist-equiv-example))))


;; (defthm-4v-sexpr-flag
;;   (defthm 4v-sexpr-eval-4v-sexpr-restrict
;;    (equal (4v-sexpr-eval (4v-sexpr-restrict x al1) al2)
;;           (4v-sexpr-eval x (append (4v-sexpr-eval-alist al1 al2)
;;                                 al2)))
;;    :flag sexpr)
;;   (defthm 4v-sexpr-eval-list-sexpr-4v-sexpr-restrict-list
;;    (equal (4v-sexpr-eval-list (4v-sexpr-restrict-list x al1) al2)
;;           (4v-sexpr-eval-list x (append (4v-sexpr-eval-alist al1 al2)
;;                                         al2)))
;;    :flag sexpr-list)
;;   :hints (("goal"
;;            :in-theory (disable 4v-sexpr-eval)
;;            :expand ((:free (al) (4v-sexpr-eval x al))
;;                     (:free (al) (4v-sexpr-eval nil al))
;;                     (:free (al x y) (4v-sexpr-eval (cons x y) al)))
;;            :do-not-induct t))
;;   :otf-flg t)




;; (defthm sexpr-var-val-alistp-eval-of-append
;;   (implies (and (sexpr-var-val-alistp map)
;;                 (subsetp-equal (alist-vals map)
;;                                (alist-keys a)))
;;            (alist-equiv (4v-sexpr-eval-alist
;;                          map (append a b))
;;                         (append (4v-sexpr-eval-alist map a)
;;                                 (4v-sexpr-eval-alist map b))))
;;   :hints (("goal" :in-theory (e/d (alist-equiv-iff-agree-on-bad-guy
;;                                    hons-assoc-equal-iff-member-alist-keys)
;;                                   (alist-keys-member-hons-assoc-equal
;;                                    4v-fix 4v-sexpr-eval))
;;            :do-not-induct t)
;;           (witness :ruleset set-reasoning-no-consp)))


;; (defthm alist-keys-translate-domain-when-covered
;;   (implies (and (unique-mapping map)
;;                 (subsetp-equal (alist-keys fp)
;;                                (alist-keys map)))


(defthm eval-map-append-translate-lemma
  (implies (and (unique-mapping map)
                (subsetp-equal (alist-keys (double-rewrite fpev))
                               (alist-keys map))
                (sexpr-var-val-alistp map))
           (4v-env-equiv (4v-sexpr-eval-alist
                          map (append
                               (translate-domain fpev map) env))
                         (append fpev (4v-sexpr-eval-alist map env))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable 4v-fix 4v-sexpr-eval))
          (witness :ruleset 4v-env-equiv-witnessing)
          (and stable-under-simplificationp
               '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                 (alist-keys-member-hons-assoc-equal))))
          (set-reasoning)))


(defexample 4v-sexpr-equiv-eval-ex
  :pattern (4v-sexpr-eval x env)
  :templates (env)
  :instance-rulename 4v-sexpr-equiv-instancing)

(defthm 4v-sexpr-fixpointp-translate-domain
  (implies (and (unique-mapping map)
                (subsetp-equal (alist-keys ups) (alist-keys map))
                (4v-sexpr-fixpointp ups fp)
                (keys-equiv ups (double-rewrite fp))
                (sexpr-var-val-alistp map))
           (4v-sexpr-fixpointp
            (translate-domain (4v-sexpr-compose-alist ups map) map)
            (translate-domain (4v-sexpr-compose-alist fp map) map)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d ()
                           (4v-env-equiv-to-key-and-env-equiv
                            keys-equiv-when-alist-keys
                            4v-sexpr-eval)))
          (witness :ruleset 4v-sexpr-fixpointp-witnessing)
          (witness :ruleset 4v-sexpr-equiv-witnessing)
          (and stable-under-simplificationp
               '(:use ((:instance 4v-sexpr-fixpointp-necc
                                  (vals fp)
                                  (k (car (hons-rassoc-equal k0 map)))))))
          (witness :ruleset 4v-sexpr-equiv-eval-ex))
  :otf-flg t)





(defthm translate-domain-4v-sexpr-compose-alist-sexpr-fixpoints
  (implies (and (unique-mapping map)
                (subsetp-equal (alist-keys ups) (alist-keys map))
                (sexpr-var-val-alistp map))
           (4v-sexpr-alist-equiv
            (translate-domain (4v-sexpr-compose-alist (sexpr-fixpoints ups) map) map)
            (sexpr-fixpoints
             (translate-domain (4v-sexpr-compose-alist ups map) map))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (4v-sexpr-alist-equiv-is-alt)
                           (sexpr-fixpoints
                            4v-env-equiv-to-key-and-env-equiv))
           :use ((:instance 4v-sexpr-least-fixpoint-unique
                            (update-fns (translate-domain (4v-sexpr-compose-alist ups map) map))
                            (lb1 (translate-domain (4v-sexpr-compose-alist
                                                    (sexpr-fixpoints ups) map)
                                                   map))
                            (lb2 (sexpr-fixpoints
                                  (translate-domain (4v-sexpr-compose-alist ups map) map)))))))
  :otf-flg t)



(local
 (defthm 4v-sexpr-fixpoint-lower-boundp-sexpr-fixpoints-rw
   (implies (4v-sexpr-alist-equiv (double-rewrite ups)
                                  (double-rewrite ups-equiv))
            (4v-sexpr-fixpoint-lower-boundp ups (sexpr-fixpoints ups-equiv)))
   :hints(("Goal" :in-theory (disable sexpr-fixpoints)))))

(local
 (defthm 4v-sexpr-fixpointp-sexpr-fixpoints-rw
   (implies (4v-sexpr-alist-equiv (double-rewrite ups)
                                  (double-rewrite ups-equiv))
            (4v-sexpr-fixpointp ups (sexpr-fixpoints ups-equiv)))
   :hints(("Goal" :in-theory (disable sexpr-fixpoints)))))

(defcong 4v-sexpr-alist-equiv 4v-sexpr-alist-equiv (sexpr-fixpoints ups) 1
  :hints (("goal" :do-not-induct t
           :in-theory (e/d () (sexpr-fixpoints))
           :use ((:instance 4v-sexpr-least-fixpoint-unique
                            (update-fns ups)
                            (lb1 (sexpr-fixpoints ups))
                            (lb2 (sexpr-fixpoints ups-equiv)))))))



(defthm 4v-sexpr-compose-alist-commute-over-translate-domain
  (equal (4v-sexpr-compose-alist (translate-domain ups a) b)
         (translate-domain (4v-sexpr-compose-alist ups b) a)))

(defthm subsetp-equal-alist-keys-translate-domain
  (subsetp-equal (alist-keys (translate-domain al map))
                 (alist-vals map))
  :hints ((set-reasoning)))

(defthm sexpr-var-val-alistp-reverse-alist
  (implies (sexpr-var-key-alistp alist)
           (sexpr-var-val-alistp (reverse-alist alist))))

(defthm 4v-sexpr-fixpoint-lower-boundp-sexpr-fixpoint-with-varmap
  (4v-sexpr-fixpoint-lower-boundp
   ups (sexpr-fixpoint-with-varmap ups map))
  :hints (("goal" :do-not-induct t
           :in-theory (disable sexpr-fixpoints
                               sexpr-fixpoints-impl-matches-spec)))
  :otf-flg t)



(defthm 4v-sexpr-fixpointp-sexpr-fixpoint-with-varmap
  (4v-sexpr-fixpointp ups (sexpr-fixpoint-with-varmap ups map))
  :hints (("goal" :do-not-induct t
           :in-theory (disable sexpr-fixpoints
                               sexpr-fixpoints-impl-matches-spec
                               4v-sexpr-fixpointp-is-alt1)))
  :otf-flg t)


(defthm 4v-sexpr-vars-list-alist-vals-translate-domain
  (implies (not (member-equal x (4v-sexpr-vars-list (alist-vals al))))
           (not (member-equal x (4v-sexpr-vars-list (alist-vals (translate-domain
                                                              al map)))))))


(defthm 4v-sexpr-vars-lookup-in-sexpr-var-val-alistp
  (implies (sexpr-var-val-alistp al)
           (equal (4v-sexpr-vars (cdr (hons-assoc-equal x al)))
                  (and (hons-assoc-equal x al)
                       (set::insert (cdr (hons-assoc-equal x al)) nil)))))


(defthm-4v-sexpr-flag
  (defthm 4v-sexpr-vars-4v-sexpr-compose-reverse-alist
    (implies (and (not (member-equal (car (hons-rassoc-equal v al))
                                     (4v-sexpr-vars x)))
                  (sexpr-var-val-alistp al)
                  (unique-mapping al))
             (not (member-equal v (4v-sexpr-vars (4v-sexpr-compose x al)))))
    :flag sexpr)
  (defthm 4v-sexpr-vars-list-4v-sexpr-compose-list-reverse-alist
    (implies (and (not (member-equal (car (hons-rassoc-equal v al))
                                     (4v-sexpr-vars-list x)))
                  (sexpr-var-val-alistp al)
                  (unique-mapping al))
             (not (member-equal v (4v-sexpr-vars-list (4v-sexpr-compose-list x al)))))
    :flag sexpr-list))

(defthm 4v-sexpr-vars-4v-sexpr-compose-alist-reverse-alist
  (implies (and (not (member-equal (car (hons-rassoc-equal v al))
                                   (4v-sexpr-vars-list (alist-vals x))))
                (sexpr-var-val-alistp al)
                (unique-mapping al))
           (not (member-equal v (4v-sexpr-vars-list (alist-vals
                                                  (4v-sexpr-compose-alist x al)))))))


(defthm 4v-sexpr-vars-reverse-alist-when-var-keys
  (implies (sexpr-var-key-alistp map)
           (iff (member-equal x (4v-sexpr-vars-list (alist-vals (reverse-alist
                                                              map))))
                (member-equal x (alist-keys map))))
  :hints(("Goal" :in-theory (enable alist-keys))))

(defthmd hons-assoc-equal-when-subsetp-alist-keys
  (implies (and (subsetp-equal (alist-keys a) (alist-keys b))
                (hons-assoc-equal k a))
           (hons-assoc-equal k b))
  :hints(("Goal" :in-theory (enable subsetp-equal alist-keys))))


(defthm keys-not-present-in-sexpr-fixpoint-with-varmap
  (implies (member-equal x (alist-keys ups))
           (not (member-equal x (4v-sexpr-vars-list (alist-vals
                                                  (sexpr-fixpoint-with-varmap
                                                   ups map))))))
  :hints(("Goal" :in-theory (e/d (hons-assoc-equal-when-subsetp-alist-keys)
                                 (sexpr-fixpoints))
          :do-not-induct t)))

(defthm-4v-sexpr-flag
  (defthm nonnil-4v-sexpr-vars
    (not (member-equal nil (4v-sexpr-vars x)))
    :flag sexpr)
  (defthm nonnil-4v-sexpr-vars-list
    (not (member-equal nil (4v-sexpr-vars-list x)))
    :flag sexpr-list))


(defthm fixpoint-with-varmap-vars-are-vars-of-update-fns
  (implies (not (member-equal x (4v-sexpr-vars-list (alist-vals
                                                  update-fns))))
           (not (member-equal x (4v-sexpr-vars-list
                                 (alist-vals (sexpr-fixpoint-with-varmap
                                              update-fns map))))))
  :hints (("goal" :cases ((hons-assoc-equal x map))
           :do-not-induct t)))


(defthm keys-of-sexpr-fixpoint-with-varmap
  (iff (hons-assoc-equal x (sexpr-fixpoint-with-varmap ups map))
       (hons-assoc-equal x ups)))







(in-theory (disable sexpr-fixpoint-with-varmap))

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

