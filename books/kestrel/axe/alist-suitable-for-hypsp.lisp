; Checking that an alist is suitable for attempting to relieve some hyps
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "axe-rules") ;todo: reduce
(include-book "rewriter-common") ; for axe-bind-free-result-okayp, todo: split that out?
(include-book "kestrel/utilities/all-vars-in-term-bound-in-alistp" :dir :system)
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))

(local (in-theory (disable symbol-alistp append)))

;; Checks whether the keys of ALIST are suitable upon reaching HYPS and
;; attempting to relieve them.
(defund alist-suitable-for-hypsp (alist hyps)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (axe-rule-hyp-listp hyps))
                  :guard-hints (("Goal" :in-theory (enable SYMBOL-ALISTP)))))
  (bound-vars-suitable-for-hypsp (strip-cars alist) hyps))

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

(defthm all-vars-in-terms-bound-in-alistp-of-fargs-of-cadr-of-car-when-axe-bind-free
  (implies (and (eq :axe-bind-free (ffn-symb (first hyps)))
                (alist-suitable-for-hypsp alist hyps)
                (axe-rule-hyp-listp hyps)
                (symbol-alistp alist))
           (all-vars-in-terms-bound-in-alistp (fargs (cadr (first hyps))) ;strip the :axe-bind-free
                                             alist))
  :hints (("Goal" :expand ((bound-vars-suitable-for-hypsp (strip-cars alist)
                                                          hyps)
                           (axe-rule-hyp-listp hyps)
                           (vars-in-term (cadr (car hyps))))
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
                (axe-bind-free-result-okayp result (cddr (car hyps)) dag-len) ;free var
                )
           (alist-suitable-for-hypsp (append result alist) (cdr hyps)))
  :hints (("Goal" :expand ((bound-vars-suitable-for-hypsp (strip-cars alist)
                                                          hyps)
                           (axe-rule-hyp-listp hyps)
                           (vars-in-term (cadr (car hyps))))
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

;; ;; Shows that the alist is still good after we extend it
;; (defthm alist-suitable-for-hypsp-of-append-and-cdr-when-free-vars
;;   (implies (and (eq :free-vars (ffn-symb (first hyps)))
;;                 (alist-suitable-for-hypsp alist hyps)
;;                 (axe-rule-hyp-listp hyps)
;;                 (symbol-alistp alist))
;;            (alist-suitable-for-hypsp (append result alist) (cdr hyps)))
;;   :hints (("Goal" :expand ((bound-vars-suitable-for-hypsp (strip-cars alist)
;;                                                           hyps)
;;                            (axe-rule-hyp-listp hyps)
;;                            (vars-in-term (cadr (car hyps))))
;;            :in-theory (enable ;all-vars-in-term-bound-in-alistp
;;                        alist-suitable-for-hypsp
;;                        bound-vars-suitable-for-hypsp
;;                        bound-vars-suitable-for-hypp
;;                        axe-rule-hypp
;;                        axe-bind-free-function-applicationp
;;                        BOUND-VARS-AFTER-HYP
;;                        axe-bind-free-result-okayp-rewrite))))

(defthm all-vars-in-term-bound-in-alistp-of-cdr-of-car-when-normal
  (implies (and (not (eq :axe-syntaxp (ffn-symb (first hyps))))
                (not (eq :axe-bind-free (ffn-symb (first hyps))))
                (not (eq :free-vars (ffn-symb (first hyps))))
                (consp hyps)
                (alist-suitable-for-hypsp alist hyps)
                (axe-rule-hyp-listp hyps)
                (symbol-alistp alist))
           (all-vars-in-term-bound-in-alistp (first hyps) alist))
  :hints (("Goal" :expand ((bound-vars-suitable-for-hypsp (strip-cars alist)
                                                          hyps)
                           (axe-rule-hyp-listp hyps))
           :in-theory (enable ;all-vars-in-term-bound-in-alistp
                       alist-suitable-for-hypsp
                       bound-vars-suitable-for-hypsp
                       bound-vars-suitable-for-hypp
                       axe-rule-hypp))))
