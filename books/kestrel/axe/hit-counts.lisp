; Counting how many times rewrite rules apply
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains utilities for counting successful rule applications
;; ("hits") using a custom property list world.

;; TODO: See also count-worlds.lisp.  Can we just use that machinery?
;; TODO: Or generalize this machinery to count things other than counts, eg.,
;; useful and useles tries.

;; TODO: Consider just using a fast alist.

(include-book "kestrel/typed-lists-light/all-consp" :dir :system)
(include-book "kestrel/alists-light/uniquify-alist-eq" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/utilities/acons-fast" :dir :system)
(include-book "merge-sort-by-cdr-greater")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local
  (defthm symbol-alistp-of-evens
    (implies (symbol-alistp alist)
             (symbol-alistp (evens alist)))
    :hints (("Goal" :induct t
             :in-theory (enable symbol-alistp evens)))))

(local
  (defthm symbol-alistp-of-odds
    (implies (symbol-alistp alist)
             (symbol-alistp (odds alist)))
    :hints (("Goal" :induct t
             :in-theory (enable symbol-alistp odds)))))

(local
  (defthm symbol-alistp-of-merge-by-cdr->
    (implies (and (symbol-alistp l1)
                  (symbol-alistp l2)
                  (symbol-alistp acc))
             (symbol-alistp (merge-by-cdr-> l1 l2 acc)))
    :hints (("Goal" :in-theory (enable merge-by-cdr->)))))

(local
  (defthm symbol-alistp-of-merge-sort-by-cdr->
    (implies (symbol-alistp alist)
             (symbol-alistp (merge-sort-by-cdr-> alist)))
    :hints (("Goal" :in-theory (enable merge-sort-by-cdr->)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthm nat-listp-of-strip-cdrs-of-evens
    (implies (nat-listp (strip-cdrs alist))
             (nat-listp (strip-cdrs (evens alist))))
    :hints (("Goal" :induct t
             :in-theory (enable nat-listp evens)))))

(local
  (defthm nat-listp-of-strip-cdrs-of-odds
    (implies (nat-listp (strip-cdrs alist))
             (nat-listp (strip-cdrs (odds alist))))
    :hints (("Goal" :induct t
             :in-theory (enable nat-listp odds)))))

(local
  (defthm nat-listp-of-strip-cdrs-of-merge-by-cdr->
    (implies (and (nat-listp (strip-cdrs l1))
                  (nat-listp (strip-cdrs l2))
                  (nat-listp (strip-cdrs acc)))
             (nat-listp (strip-cdrs (merge-by-cdr-> l1 l2 acc))))
    :hints (("Goal" :in-theory (enable merge-by-cdr->)))))

(local
  (defthm nat-listp-of-strip-cdrs-of-merge-sort-by-cdr->
    (implies (nat-listp (strip-cdrs alist))
             (nat-listp (strip-cdrs (merge-sort-by-cdr-> alist))))
    :hints (("Goal" :in-theory (enable merge-sort-by-cdr->)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A true-list of triples of the form (sym prop . nat).  See :doc world.  A
;; specialization of plist-worldp that requires the values to be nats.
;; Note that nil satisfies hit-countsp but means that we are not counting hits
;; at all (see empty-hit-counts).  Every valid hit-counts will have an entry
;; for the special key :fake.  So we could perhaps call this maybe-hit-countsp.
(defund hit-countsp (alist)
  (declare (xargs :guard t))
  (cond ((atom alist) (eq alist nil))
        (t (and (consp (car alist))
                (symbolp (car (car alist)))
                (consp (cdr (car alist)))
                (symbolp (cadr (car alist)))
                (natp (cddr (car alist)))
                (hit-countsp (cdr alist))))))

;limit?
(local
  (defthm plist-worldp-when-hit-countsp
    (implies (hit-countsp alist)
             (plist-worldp alist))
    :hints (("Goal" :in-theory (enable hit-countsp plist-worldp)))))

(local
  (defthm natp-of-getprop-when-hit-countsp
    (implies (and (hit-countsp hit-counts)
                  (natp val))
             (natp (sgetprop rule-symbol key val world-name hit-counts)))
    :hints (("Goal" :in-theory (enable hit-countsp)))))

(local
  (defthm hit-countsp-of-uniquify-alist-eq-aux
    (implies (and (hit-countsp hit-counts)
                  (hit-countsp acc))
             (hit-countsp (uniquify-alist-eq-aux hit-counts acc)))
    :hints (("Goal" :in-theory (enable hit-countsp acons)))))

(local
  (defthmd symbol-alistp-when-hit-countsp
    (implies (hit-countsp hit-counts)
             (symbol-alistp hit-counts))
    :hints (("Goal" :in-theory (enable hit-countsp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Consider not calling extend-world each time (instead, maybe try every 20 times).
(defund increment-hit-count (rule-symbol hit-counts)
  (declare (xargs :guard (and (symbolp rule-symbol)
                              (hit-countsp hit-counts))))
    (let* ((count (the (integer 0 *) (getprop rule-symbol 'hit-count 0 'hit-counts hit-counts)))
           (count (the (integer 0 *) (+ 1 count)))
           (hit-counts (extend-world 'hit-counts (putprop rule-symbol 'hit-count count hit-counts))))
      hit-counts))

(local
  (defthm hit-countsp-of-increment-hit-count
    (implies (and (hit-countsp hit-counts)
                  (symbolp rule-symbol))
             (hit-countsp (increment-hit-count rule-symbol hit-counts)))
    :hints (("Goal" :in-theory (enable increment-hit-count hit-countsp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;rename
;; We inline this to optimize the case when hit-counts is nil.
;; We keep this disabled to avoid case splits in proofs about code that calls it.
(defund-inline maybe-increment-hit-count (rule-symbol hit-counts)
  (declare (xargs :guard (and (symbolp rule-symbol)
                              (hit-countsp hit-counts) ; allows nil, meaning no hit-counts
                              )))
  ;; if hit-counts is nil, it remains so:
  (and hit-counts (increment-hit-count rule-symbol hit-counts)))

(defthm hit-countsp-of-maybe-increment-hit-count
  (implies (and (hit-countsp hit-counts)
                (symbolp rule-symbol))
           (hit-countsp (maybe-increment-hit-count rule-symbol hit-counts)))
  :hints (("Goal" :in-theory (enable maybe-increment-hit-count))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund empty-hit-counts ()
  (declare (xargs :guard t))
  (prog2$ (retract-world 'hit-counts nil)
          ;setting :fake means that hit-counts is nil iff we are not tracking the hit-counts
          (increment-hit-count :fake nil)))

;; Disabled since this is a ground term
(defthmd hit-countsp-of-empty-hit-counts
  (hit-countsp (empty-hit-counts)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund hit-count-alistp (alist)
  (declare (xargs :guard t))
  (and (symbol-alistp alist)
       (nat-listp (strip-cdrs alist))))

(local
  (defthm hit-count-alistp-forward-to-symbol-alistp
    (implies (hit-count-alistp alist)
             (symbol-alistp alist))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable hit-count-alistp)))))

(local
  (defthm hit-count-alistp-of-cdr
    (implies (hit-count-alistp alist)
             (hit-count-alistp (cdr alist)))
    :hints (("Goal" :in-theory (enable hit-count-alistp)))))

(local
  (defthm hit-count-alistp-forward-to-all-consp
    (implies (hit-count-alistp alist)
             (all-consp alist))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable hit-count-alistp)))))

(local
  (defthm all-cdrs-rationalp-when-hit-count-alistp
    (implies (hit-count-alistp alist)
             (all-cdrs-rationalp alist))
    :hints (("Goal" :in-theory (enable hit-count-alistp)))))

(local
  (defthmd natp-of-lookup-equal-when-hit-count-alistp
    (implies (hit-count-alistp alist)
             (or (natp (lookup-equal sym alist))
                 (not (lookup-equal sym alist))))
    :rule-classes :type-prescription
    :otf-flg t
    :hints (("Goal" :in-theory (e/d (hit-count-alistp lookup-equal assoc-equal STRIP-CDRS) (CDR-IFF))))))

(local
  (defthmd nat-of-cdr-of-car-when-hit-count-alistp
    (implies (and (hit-count-alistp alist)
                  (consp alist))
             (natp (cdr (car alist))))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (e/d (hit-count-alistp lookup-equal assoc-equal STRIP-CDRS) (CDR-IFF))))))

;; (local
;;   (defthmd consp-car-when-hit-count-alistp
;;     (implies (and (hit-count-alistp alist)
;;                   (consp alist))
;;              (consp (car alist)))
;;     :rule-classes :type-prescription
;;     :hints (("Goal" :in-theory (e/d (hit-count-alistp lookup-equal assoc-equal STRIP-CDRS) (CDR-IFF))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The hit-counts should be uniquify-ed before calling this.
;; This gets rid of the mention of :fake.
(defund make-hit-count-alist-aux (hit-counts acc)
  (declare (xargs :guard (and (hit-countsp hit-counts)
                              (alistp acc))
                  :guard-hints (("Goal" :in-theory (enable hit-countsp)))))
  (if (endp hit-counts)
      acc
    (let* ((entry (car hit-counts))
           (symbol (car entry))
           ;;(key (cadr entry)) ;should be 'hit-count
           (hit-count (cddr entry)))
      (make-hit-count-alist-aux (cdr hit-counts) (if (eq :fake symbol) acc (acons-fast symbol hit-count acc))))))

(local
  (defthm hit-count-alistp-of-make-hit-count-alist-aux
    (implies (and (hit-countsp hit-counts)
                  (hit-count-alistp acc))
             (hit-count-alistp (make-hit-count-alist-aux hit-counts acc)))
    :hints (("Goal" :in-theory (enable hit-count-alistp symbol-alistp strip-cdrs hit-countsp
                                       make-hit-count-alist-aux)))))

;; (local
;;   (defthm all-consp-of-make-hit-count-alist-aux
;;     (implies (all-consp acc)
;;              (all-consp (make-hit-count-alist-aux hit-counts acc)))
;;     :hints (("Goal" :in-theory (enable make-hit-count-alist-aux)))))

;; (local
;;   (defthm true-listp-of-make-hit-count-alist-aux
;;     (implies (true-listp acc)
;;              (true-listp (make-hit-count-alist-aux hit-counts acc)))
;;     :hints (("Goal" :in-theory (enable make-hit-count-alist-aux)))))

;; (local
;;   (defthm alistp-of-make-hit-count-alist-aux
;;     (implies (alistp acc)
;;              (alistp (make-hit-count-alist-aux hit-counts acc)))
;;     :hints (("Goal" :in-theory (enable make-hit-count-alist-aux)))))

;; (local
;;   (defthm all-cdrs-rationalp-of-make-hit-count-alist-aux
;;     (implies (and (hit-countsp hit-counts)
;;                   (all-cdrs-rationalp acc))
;;              (all-cdrs-rationalp (make-hit-count-alist-aux hit-counts acc)))
;;     :hints (("Goal" :in-theory (enable hit-countsp make-hit-count-alist-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This gets rid of the mention of :fake.
(defund make-hit-count-alist (hit-counts)
  (declare (xargs :guard (hit-countsp hit-counts)))
  (make-hit-count-alist-aux (uniquify-alist-eq hit-counts) nil))

(defthm hit-count-alistp-of-make-hit-count-alist
  (implies (hit-countsp hit-counts)
           (hit-count-alistp (make-hit-count-alist hit-counts)))
  :hints (("Goal" :in-theory (enable make-hit-count-alist))))

;; todo: do we need all these type rules?

;; (defthm all-consp-of-make-hit-count-alist
;;   (all-consp (make-hit-count-alist hit-counts))
;;   :hints (("Goal" :in-theory (enable make-hit-count-alist))))

;; (defthm true-listp-of-make-hit-count-alist
;;   (true-listp (make-hit-count-alist hit-counts))
;;   :hints (("Goal" :in-theory (enable make-hit-count-alist))))

;; (defthm alistp-of-make-hit-count-alist
;;   (alistp (make-hit-count-alist hit-counts))
;;   :hints (("Goal" :in-theory (enable make-hit-count-alist))))

;; (defthm all-cdrs-rationalp-of-make-hit-count-alist
;;   (implies (hit-countsp hit-counts)
;;            (all-cdrs-rationalp (make-hit-count-alist hit-counts)))
;;   :hints (("Goal" :in-theory (enable hit-countsp make-hit-count-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund sort-hit-count-alist (alist)
  (declare (xargs :guard (hit-count-alistp alist)))
  (merge-sort-by-cdr-> alist))

(defthm hit-count-alistp-of-sort-hit-count-alist
  (implies (hit-count-alistp alist)
           (hit-count-alistp (sort-hit-count-alist alist)))
  :hints (("Goal" :in-theory (enable hit-count-alistp sort-hit-count-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Consider optimizing this by looping through all the rule names and
;; just looking up their counts, instead of calling uniquify-alist-eq.
;; Returns a hit-count-alist mapping rule names to hit counts.
(defund summarize-hit-counts (hit-counts)
  (declare (xargs :guard (hit-countsp hit-counts)))
  (let* (; (hit-counts (uniquify-alist-eq hit-counts)) ;does this not use the fast lookup into the hit-counts?
         (hit-count-alist (make-hit-count-alist hit-counts))
         ) ;removes shadowed bindings
    (sort-hit-count-alist hit-count-alist)))

;; (local
;;   (defthm alistp-of-summarize-hit-counts
;;     (implies (hit-countsp hit-counts)
;;              (alistp (summarize-hit-counts hit-counts)))
;;     :hints (("Goal" :in-theory (enable summarize-hit-counts
;;                                        hit-countsp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: handle or disallow print=nil
(defund maybe-print-hit-counts (print hit-counts)
  (declare (xargs :guard (and ;; something about print
                          (hit-countsp hit-counts))))
  (if (not hit-counts)
      nil ;; We are not counting hits, so do nothing
    (let ((num-hits (+ -1 (len hit-counts)))) ; each item in the HIT-COUNTS represents one hit, but remove the entry for :fake
      ;; TODO: We are transitioning to not counting hits for :brief printing
      (if (eq :brief print)
          ;; Just print the number of hits (TODO: In this case, we could keep a simple count of hits, rather than counting the hits of each rule):
          (if (= 0 num-hits)
              (cw "(No hits.)")
            (if (eql 1 num-hits)
                (cw "(1 hit.)")
              (cw "(~x0 hits.)" num-hits)))
        ;; Print the rules and their hit counts:
        (progn$ (if (= 0 num-hits)
                    (cw "(No hits.)")
                  (if (eql 1 num-hits)
                      (cw "(1 hit:~%~y0)" (summarize-hit-counts hit-counts))
                    (cw "(~x0 hits:~%~y1)" num-hits (summarize-hit-counts hit-counts))))
                ;;todo: put this back but make it a separate option, off by default:
                ;; (let* ((useful-rules (strip-cars rule-count-alist))
                ;;        (useless-rules (set-difference-eq all-rule-names useful-rules)))
                ;;   (cw "(~x0 Useless rules: ~x1.)~%" (len useless-rules) useless-rules)
                ;;   )
                )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Make a hit count alist where each rule's count is its count in alist1 minus
;; its count in alist2.  We expect alist1 to be an "superset" (in the sense of
;; each rule having at least as many hits) of alist2, so the subtractions will
;; never give negative numbers, but we just call nfix to enforce that.
(defund subtract-hit-count-alists (alist1 alist2)
  (declare (xargs :guard (and (hit-count-alistp alist1)
                              (hit-count-alistp alist2))
                  :guard-hints (("Goal" :in-theory (enable HIT-COUNT-ALISTP)))
                  :verify-guards nil ;; done below
                  ))
  (if (endp alist1)
      nil
    (let* ((entry (car alist1))
           (sym (car entry))
           (count (cdr entry))
           (maybe-other-count (lookup-eq sym alist2))
           (other-count (if maybe-other-count maybe-other-count 0))
           (count-diff (nfix (- count other-count))) ;we don't let it go negative
           )
      (if (posp count-diff)
          (acons sym count-diff (subtract-hit-count-alists (rest alist1) alist2))
        ;; skip things with 0 count:
        (subtract-hit-count-alists (rest alist1) alist2)))))

(defthm hit-count-alistp-of-subtract-hit-count-alists
  (implies (and (hit-count-alistp alist1)
                (hit-count-alistp alist2))
           (hit-count-alistp (subtract-hit-count-alists alist1 alist2)))
  :hints (("Goal" :in-theory (enable hit-count-alistp subtract-hit-count-alists))))

;; (local
;;   (defthm alistp-of-subtract-hit-count-alists
;;     (alistp (subtract-hit-count-alists alist1 alist2))
;;     :hints (("Goal" :in-theory (enable hit-count-alistp subtract-hit-count-alists)))))

(verify-guards subtract-hit-count-alists
  :hints (("Goal" :in-theory (enable nat-of-cdr-of-car-when-hit-count-alistp
                                     natp-of-lookup-equal-when-hit-count-alistp))))

;; (local
;;   (defthm all-cdrs-rationalp-of-subtract-hit-count-alists
;;     (implies (and (hit-count-alistp alist1)
;;                   (hit-count-alistp alist2))
;;              (all-cdrs-rationalp (subtract-hit-count-alists alist1 alist2)))))
