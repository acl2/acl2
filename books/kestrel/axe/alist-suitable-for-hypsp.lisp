; Checking that an alist is suitable for attempting to relieve some hyps
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "axe-rules")
(include-book "axe-bind-free-result-okayp")
(include-book "kestrel/utilities/all-vars-in-term-bound-in-alistp" :dir :system)
(include-book "match-hyp-with-nodenum-to-assume-false")
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/memberp" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/list-sets" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (in-theory (disable symbol-alistp append)))

;move
;; (thm
;;  (implies (not (intersection-equal x y))
;;           (perm (union-equal x y)
;;                 (append x y))))

(local (in-theory (disable intersection-equal strip-cars)))

;move
(defthm memberp-of-car-and-strip-cars
  (implies (memberp a x)
           (memberp (car a) (strip-cars x)))
  :hints (("Goal" :in-theory (enable strip-cars
                                     memberp))))

;move
(local
 (defthm strip-cars-of-remove1-equal-perm
  (implies (memberp a x)
           (perm (strip-cars (remove1-equal a x))
                 (remove1-equal (car a) (strip-cars x))))
  :hints (("Goal" :in-theory (enable remove1-equal strip-cars memberp)))))

;move
(defcong perm perm (strip-cars x) 1
  :hints (("Goal" :in-theory (enable strip-cars perm))))

;;;
;;; alist-suitable-for-hypsp
;;;

;; Checks whether the keys of ALIST are suitable upon reaching HYPS and
;; attempting to relieve them.
(defund alist-suitable-for-hypsp (alist hyps)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (axe-rule-hyp-listp hyps))
                  :guard-hints (("Goal" :in-theory (enable SYMBOL-ALISTP)))))
  (bound-vars-suitable-for-hypsp (strip-cars alist) hyps))

(defthm alist-suitable-for-hypsp-when-axe-sytaxp-car
  (implies (equal :axe-syntaxp (car (car hyps)))
           (equal (alist-suitable-for-hypsp alist hyps)
                  (and (subsetp-equal (free-vars-in-term (cdr (car hyps))) (strip-cars alist))
                       (alist-suitable-for-hypsp alist (cdr hyps)))))
  :hints (("Goal" :in-theory (enable alist-suitable-for-hypsp))))

(defthm all-vars-in-term-bound-in-alistp-of-cdr-of-car-when-axe-sytaxp
  (implies (and (eq :axe-syntaxp (ffn-symb (first hyps)))
                (alist-suitable-for-hypsp alist hyps)
                (axe-rule-hyp-listp hyps)
                (symbol-alistp alist))
           (all-vars-in-term-bound-in-alistp (cdr (first hyps)) ;strip the :axe-syntaxp
                                             alist))
  :hints (("Goal" :expand ((bound-vars-suitable-for-hypsp (strip-cars alist)
                                                          hyps)
                           (axe-rule-hyp-listp hyps))
           :in-theory (enable ;all-vars-in-term-bound-in-alistp
                       alist-suitable-for-hypsp
                       bound-vars-suitable-for-hypsp
                       bound-vars-suitable-for-hypp
                       axe-rule-hypp))))

(defthm subsetp-equal-of-free-vars-in-terms-of-fargs-of-cadr-of-car-when-axe-bind-free
  (implies (and (eq :axe-bind-free (ffn-symb (first hyps)))
                (alist-suitable-for-hypsp alist hyps)
                (axe-rule-hyp-listp hyps)
                (symbol-alistp alist))
           ;(all-vars-in-terms-bound-in-alistp (fargs (cadr (first hyps))) ;strip the :axe-bind-free
;                                   alist)
           (subsetp-equal (free-vars-in-terms (fargs (cadr (first hyps)))) (strip-cars alist))
           )
  :hints (("Goal" :expand ((bound-vars-suitable-for-hypsp (strip-cars alist)
                                                          hyps)
                           (axe-rule-hyp-listp hyps)
                           (free-vars-in-term (cadr (car hyps))))
           :in-theory (enable ;all-vars-in-term-bound-in-alistp
                       alist-suitable-for-hypsp
                       bound-vars-suitable-for-hypsp
                       bound-vars-suitable-for-hypp
                       axe-rule-hypp
                       axe-bind-free-function-applicationp))))

;; Shows that the alist is still good after we extend it
(defthm alist-suitable-for-hypsp-of-append-and-cdr-when-axe-bind-free
  (implies (and (eq :axe-bind-free (ffn-symb (first hyps)))
                (alist-suitable-for-hypsp alist hyps)
                (axe-rule-hyp-listp hyps)
                (symbol-alistp alist)
                result ;drop?
                ;;(axe-bind-free-result-okayp result (cddr (car hyps)) dag-len) ;free var
                (alistp result)
                (equal (cddr (car hyps)) (strip-cars result)))
           (alist-suitable-for-hypsp (append result alist) (cdr hyps)))
  :hints (("Goal" :expand ((bound-vars-suitable-for-hypsp (strip-cars alist)
                                                          hyps)
                           (axe-rule-hyp-listp hyps)
                           (free-vars-in-term (cadr (car hyps))))
           :in-theory (enable ;all-vars-in-term-bound-in-alistp
                       alist-suitable-for-hypsp
                       bound-vars-suitable-for-hypsp
                       bound-vars-suitable-for-hypp
                       axe-rule-hypp
                       axe-bind-free-function-applicationp
                       BOUND-VARS-AFTER-HYP
                       axe-bind-free-result-okayp-rewrite))))

;not sure if we need this
(defthm not-all-vars-in-term-bound-in-alistp-of-cdr-of-car-when-free-vars
  (implies (and (eq :free-vars (ffn-symb (first hyps)))
                (alist-suitable-for-hypsp alist hyps)
                (axe-rule-hyp-listp hyps)
                (symbol-alistp alist))
           (not (all-vars-in-term-bound-in-alistp (cdr (first hyps)) ;strip the :free-vars
                                                  alist)))
  :hints (("Goal" :expand ((bound-vars-suitable-for-hypsp (strip-cars alist)
                                                          hyps)
                           (axe-rule-hyp-listp hyps))
           :in-theory (enable ;all-vars-in-term-bound-in-alistp
                       alist-suitable-for-hypsp
                       bound-vars-suitable-for-hypsp
                       bound-vars-suitable-for-hypp
                       axe-rule-hypp))))

;; Shows that the alist is still good after we extend it
(defthm alist-suitable-for-hypsp-of-append-and-cdr-when-free-vars
  (implies (and (eq :free-vars (ffn-symb (first hyps)))
                (alist-suitable-for-hypsp alist hyps)
                (axe-rule-hyp-listp hyps)
                (symbol-alistp alist)
                ;; result binds exactly the remaining free vars in the hyp:
                (perm (strip-cars result)
                      (set-difference-equal (free-vars-in-term (cdr (car hyps)))
                                            (strip-cars alist))))
           (alist-suitable-for-hypsp (append result alist) ; can call append because the var sets are disjoint
                                     (cdr hyps)))
  :hints (("Goal" :expand ((bound-vars-suitable-for-hypsp (strip-cars alist)
                                                          hyps)
                           (axe-rule-hyp-listp hyps)
                           (free-vars-in-term (cadr (car hyps))))
           :in-theory (enable ;all-vars-in-term-bound-in-alistp
                       alist-suitable-for-hypsp
                       bound-vars-suitable-for-hypsp
                       bound-vars-suitable-for-hypp
                       axe-rule-hypp
                       axe-bind-free-function-applicationp
                       BOUND-VARS-AFTER-HYP
                       axe-bind-free-result-okayp-rewrite))))

;drop?
;; (defthm all-vars-in-term-bound-in-alistp-of-car-when-normal
;;   (implies (and (not (eq :axe-syntaxp (ffn-symb (first hyps))))
;;                 (not (eq :axe-bind-free (ffn-symb (first hyps))))
;;                 (not (eq :free-vars (ffn-symb (first hyps))))
;;                 (consp hyps)
;;                 (alist-suitable-for-hypsp alist hyps)
;;                 (axe-rule-hyp-listp hyps)
;;                 (symbol-alistp alist))
;;            (all-vars-in-term-bound-in-alistp (first hyps) alist))
;;   :hints (("Goal" :expand ((bound-vars-suitable-for-hypsp (strip-cars alist)
;;                                                           hyps)
;;                            (axe-rule-hyp-listp hyps))
;;            :in-theory (enable ;all-vars-in-term-bound-in-alistp
;;                        alist-suitable-for-hypsp
;;                        bound-vars-suitable-for-hypsp
;;                        bound-vars-suitable-for-hypp
;;                        axe-rule-hypp))))

(defthm subsetp-equal-of-free-vars-in-term-of-car-and-strip-cars-when-normal
  (implies (and (not (eq :axe-syntaxp (ffn-symb (first hyps))))
                (not (eq :axe-bind-free (ffn-symb (first hyps))))
                (not (eq :free-vars (ffn-symb (first hyps))))
                (consp hyps)
                (alist-suitable-for-hypsp alist hyps)
                (axe-rule-hyp-listp hyps)
                (symbol-alistp alist))
           (subsetp-equal (free-vars-in-term (first hyps)) (strip-cars alist)))
  :hints (("Goal" :expand ((bound-vars-suitable-for-hypsp (strip-cars alist)
                                                          hyps)
                           (axe-rule-hyp-listp hyps))
           :in-theory (enable ;all-vars-in-term-bound-in-alistp
                       alist-suitable-for-hypsp
                       bound-vars-suitable-for-hypsp
                       bound-vars-suitable-for-hypp
                       axe-rule-hypp))))

(defthm alist-suitable-for-hypsp-of-cdr-of-car-when-normal
  (implies (and (not (eq :axe-syntaxp (ffn-symb (first hyps))))
                (not (eq :axe-bind-free (ffn-symb (first hyps))))
                (not (eq :free-vars (ffn-symb (first hyps))))
                (consp hyps)
                (alist-suitable-for-hypsp alist hyps)
                (axe-rule-hyp-listp hyps)
                (symbol-alistp alist))
           (alist-suitable-for-hypsp alist (cdr hyps)))
  :hints (("Goal" :expand ((bound-vars-suitable-for-hypsp (strip-cars alist)
                                                          hyps)
                           (axe-rule-hyp-listp hyps))
           :in-theory (enable ;all-vars-in-term-bound-in-alistp
                       alist-suitable-for-hypsp
                       bound-vars-suitable-for-hypsp
                       bound-vars-suitable-for-hypp
                       axe-rule-hypp
                       bound-vars-after-hyp))))

;;;
;;; alist-suitable-for-hyp-tree-and-hypsp
;;;

;; Checks whether ALIST and HYPS are suitable after having instantiated HYP
;; with ALIST (so we are now at the point of having to find matches to bind its
;; remaining free vars), and having HYPS as the list of hyps to be relieved
;; subsequently.
(defund alist-suitable-for-hyp-tree-and-hypsp (alist
                                               hyp ;an axe-tree, partially instantiated, so all vars from alist have been replaced
                                               hyps)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (axe-treep hyp)
                              (axe-rule-hyp-listp hyps))
                  :guard-hints (("Goal" :in-theory (enable ;SYMBOL-ALISTP
                                                           STRIP-CARS-OF-CDR)))))
  (and ;; The alist doesn't bind any vars that remain in the hyp:
   (not (intersection-eq (strip-cars alist) (axe-tree-vars hyp)))
   ;; After we bind all the vars in the hyp, the alist will be suitable for the remaining hyps:
   (bound-vars-suitable-for-hypsp (append (axe-tree-vars hyp) ; can just call append since the sets of vars are disjoint
                                          (strip-cars alist))
                                  hyps)))

(defthm alist-suitable-for-hypsp-after-matching
  (implies (and (alist-suitable-for-hyp-tree-and-hypsp alist hyp hyps)
                (not (equal :fail (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len)))
                (not (equal 'quote (ffn-symb hyp)))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum-to-assume-false dag-len)
                (natp nodenum-to-assume-false)
                (axe-treep hyp)
                (consp hyp)
                (symbol-alistp alist))
           (alist-suitable-for-hypsp (append (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len)
                                             alist)
                                     hyps))
  :hints (("Goal" :in-theory (enable alist-suitable-for-hypsp
                                     alist-suitable-for-hyp-tree-and-hypsp))))

(defthm alist-suitable-for-hyp-tree-and-hypsp-after-instantiating
  (implies (and (alist-suitable-for-hypsp alist hyps)
                (equal :free-vars (ffn-symb (car hyps)))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (axe-treep hyp)
                (consp hyp)
                (symbol-alistp alist)
                ;; (no-duplicatesp-equal (strip-cars alist)) ;gen?
                ;;(not (intersection-equal (strip-cars alist) (axe-tree-vars hyp)))
                (equal (axe-tree-vars hyp)
                       (set-difference-equal (free-vars-in-term (cdr (car hyps)))
                                             (strip-cars alist))))
           (alist-suitable-for-hyp-tree-and-hypsp alist
                                                  hyp ;instantiated
                                                  (cdr hyps)))
  :hints (("Goal"
           :use (:instance bound-vars-suitable-for-hypsp-when-free-vars-2
                           (bound-vars (STRIP-CARS ALIST)))
           :in-theory (e/d (alist-suitable-for-hypsp
                            alist-suitable-for-hyp-tree-and-hypsp)
                           (bound-vars-suitable-for-hypsp-when-free-vars-2)))))

;;;
;;; alist-suitable-for-hyp-args-and-hypsp
;;;

;; Checks whether ALIST and HYPS are suitable after having instantiated a hyp
;; with ALIST and getting its args, HYP-ARGS (so we are now at the point of
;; having to find matches to bind the hyp's remaining free vars), and having
;; HYPS as the list of hyps to be relieved subsequently.
(defund alist-suitable-for-hyp-args-and-hypsp (alist
                                               hyp-args ; axe-trees, partially instantiated, so all vars from alist have been replaced
                                               hyps)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (axe-tree-listp hyp-args)
                              (axe-rule-hyp-listp hyps))
                  :guard-hints (("Goal" :in-theory (enable symbol-alistp)))))
  (and ;; The alist doesn't bind any vars that remain in the partially-instantiated hyp's args:
   (not (intersection-eq (strip-cars alist) (axe-tree-vars-lst hyp-args)))
   ;; After we bind all the vars in the hyp-args, the alist will be suitable for the remaining hyps:
   (bound-vars-suitable-for-hypsp (append (axe-tree-vars-lst hyp-args) ; can just call append since the sets of vars are disjoint
                                          (strip-cars alist))
                                  hyps)))

(defthm alist-suitable-for-hypsp-after-matching-2
  (implies (and (alist-suitable-for-hyp-args-and-hypsp alist hyp-args hyps)
                (bounded-darg-listp arg-list dag-len)
                (not (equal :fail (unify-trees-with-dag-nodes hyp-args arg-list dag-array alist)))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (axe-tree-listp hyp-args)
                (symbol-alistp alist))
           (alist-suitable-for-hypsp (unify-trees-with-dag-nodes hyp-args arg-list dag-array alist)
                                     hyps))
  :hints (("Goal" :in-theory (enable alist-suitable-for-hypsp
                                     alist-suitable-for-hyp-args-and-hypsp))))

;; (defthm alist-suitable-for-hyp-args-and-hypsp-after-instantiating
;;   (implies (and (alist-suitable-for-hypsp alist hyps)
;;                 (equal :free-vars (ffn-symb (car hyps)))
;;                 (pseudo-dag-arrayp 'dag-array dag-array dag-len)
;;                 (axe-tree-listp hyp-args)
;;                 (symbol-alistp alist)
;;                 ;; (no-duplicatesp-equal (strip-cars alist)) ;gen?
;;                 ;;(not (intersection-equal (strip-cars alist) (axe-tree-vars hyp)))
;;                 (equal (axe-tree-vars hyp)
;;                        (set-difference-equal (free-vars-in-term (cdr (car hyps)))
;;                                              (strip-cars alist))))
;;            (alist-suitable-for-hyp-args-and-hypsp alist
;;                                                   hyp ;instantiated
;;                                                   (cdr hyps)))
;;   :hints (("Goal"
;;            :use (:instance bound-vars-suitable-for-hypsp-when-free-vars-2
;;                            (bound-vars (STRIP-CARS ALIST)))
;;            :in-theory (e/d (alist-suitable-for-hypsp
;;                             alist-suitable-for-hyp-args-and-hypsp)
;;                            (bound-vars-suitable-for-hypsp-when-free-vars-2)))))
