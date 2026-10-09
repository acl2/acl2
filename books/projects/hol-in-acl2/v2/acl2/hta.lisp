; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "alist-subsetp")
(include-book "hol-zify") ; no_port

(defun hta0 ()

; We model a list as a function whose domain is a natural number.  That way
; it's more obvious than using cons that the set of all lists from a given set
; is itself a set, without using any sort of collection or replacement (due to
; the way cons bumps up the set-theoretic rank).

  (declare (xargs :guard t))
  `((:num    . (,(omega)      . 0))
    (:bool   . (,(pair t nil) . 0))
    (:arrow  . (,(zfun-space) . 2))
    (:hash   . (,(zprod2)     . 2))
    (:list   . (,(zfinseqs)   . 1))
    (:option . (,(zoption)    . 1))
    (:ki     . (,(zki)        . 2))))

(defun hta-arities0 ()
  (declare (xargs :guard t))
  '((:num    . 0)
    (:bool   . 0)
    (:arrow  . 2)
    (:hash   . 2)
    (:list   . 1)
    (:option . 1)
    (:ki     . 2)))

(in-theory (disable (:e hta0)))

(defun hta-to-arities (hta)
  (declare (xargs :guard (and (symbol-alistp hta)
                              (alistp (strip-cdrs hta)))))
  (pairlis$ (strip-cars hta)
            (strip-cdrs (strip-cdrs hta))))

(defthm hta-to-arities-hta0
  (equal (hta-to-arities (hta0))
         (hta-arities0)))

(defun-sk hol-constructor-p (constructor arity)
  (declare (xargs :guard (posp arity)))
  (forall x
    (implies (and (in x (v-omega*2))
                  (true-listp x)
                  (equal (length x) arity)
                  (not (member 0 x)))
             (and (in (apply constructor x)
                      (v-omega*2))
                  (not (equal (apply constructor x)
                              0)))))
  :rewrite :direct)

(defun htap1 (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        (t (let* ((trip (car x)))
             (case-match trip
               ((kwd . (constructor . arity))
                (and (keywordp kwd)
                     (natp arity)
                     (cond ((equal arity 0)
                            (and (not (equal constructor 0)) ; non-empty set
                                 (in constructor (v-omega*2))))
                           (t
                            (hol-constructor-p constructor arity)))
                     (htap1 (cdr x))))
               (& nil))))))

; Start proof of htap1-hta0.

(defthmdz in-0-finseqs
  (in 0 (finseqs s))
  :props (zfc inverse$prop domain$prop prod2$prop finseqs$prop))

(defthmz not-equal-finseqs-0
  (not (equal (finseqs s)
              0))
  :hints (("Goal" :use in-0-finseqs))
  :props (zfc inverse$prop domain$prop prod2$prop finseqs$prop))

(defthmdz not-equal-fun-space-0-lemma
  (implies (not (equal s2 0))
           (in (prod2 s1 (singleton (min-in s2)))
               (fun-space s1 s2)))
  :hints (("Goal" :in-theory (enable funp)))
  :props (zfc inverse$prop domain$prop prod2$prop fun-space$prop))

(defthmz not-equal-fun-space-0
  (implies (not (equal s2 0))
           (not (equal (fun-space s1 s2) 0)))
  :hints (("Goal" :use not-equal-fun-space-0-lemma))
  :props (zfc inverse$prop domain$prop prod2$prop fun-space$prop))

(defthmdz not-equal-prod2-0-lemma
  (implies (and (not (equal s1 0))
                (not (equal s2 0)))
           (in (cons (min-in s1) (min-in s2))
               (prod2 s1 s2)))
  :props (zfc inverse$prop domain$prop prod2$prop))

(defthmz not-equal-prod2-0
  (implies (and (not (equal s1 0))
                (not (equal s2 0)))
           (not (equal (prod2 s1 s2) 0)))
  :hints (("Goal" :use not-equal-prod2-0-lemma))
  :props (zfc inverse$prop domain$prop prod2$prop))

(extend-zfc-table hta-prop
                  zfc v$prop v-omega+$prop
                  inverse$prop domain$prop
                  prod2$prop zprod2$prop
                  finseqs$prop zfinseqs$prop
                  zoption$prop
                  fun-space$prop zfun-space$prop
                  zki$prop)

(defthmz htap1-hta0
  (htap1 (hta0))
  :props (hta-prop))

(defthm htap1-implies-hol-constructor-p
  (implies (and (force (htap1 hta))
                (force (hons-assoc-equal kwd hta))
                (force (not (equal (cddr (hons-assoc-equal kwd hta)) 0))))
           (hol-constructor-p (cadr (hons-assoc-equal kwd hta))
                              (cddr (hons-assoc-equal kwd hta))))
  :hints (("Goal" :in-theory (disable hol-constructor-p))))

(defun htap (x)
  (declare (xargs :guard t))
  (and (alist-subsetp (hta0) x)
       (htap1 x)))

(defthm hta0-props
  (and (equal (hons-assoc-equal :num (hta0))
              (cons :num (cons (omega) 0)))
       (equal (hons-assoc-equal :bool (hta0))
              (cons :bool (cons (pair t nil) 0)))
       (equal (hons-assoc-equal :arrow (hta0))
              (cons :arrow (cons (zfun-space) 2)))
       (equal (hons-assoc-equal :hash (hta0))
              (cons :hash (cons (zprod2) 2)))
       (equal (hons-assoc-equal :list (hta0))
              (cons :list (cons (zfinseqs) 1)))
       (equal (hons-assoc-equal :option (hta0))
              (cons :option (cons (zoption) 1)))
       (equal (hons-assoc-equal :ki (hta0))
              (cons :ki (cons (zki) 2))))
  :hints (("Goal" :in-theory (enable hta0))))

(defthm htap1-implies-alistp
  (implies (htap1 hta)
           (alistp hta)))

(defthm alist-subsetp-preserves-non-nil
  (implies (and hta
                (alistp hta))
           (not (alist-subsetp hta nil)))
  :hints (("Goal" :expand ((alist-subsetp hta nil)))))

(defthm alist-subsetp-preserves-non-nil-forward
  (implies (and (alist-subsetp hta nil)
                (alistp hta))
           (not hta))
  :rule-classes :forward-chaining)

(in-theory (disable hol-constructor-p))
