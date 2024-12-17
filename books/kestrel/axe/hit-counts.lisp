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
;; useful and useless tries.

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
;; Note that nil satisfies hit-count-info-worldp but means that we are not counting hits
;; at all (see empty-hit-counts).  Every valid hit-counts will have an entry
;; for the special key :fake.  So we could perhaps call this maybe-hit-count-info-worldp.
(defund hit-count-info-worldp (alist)
  (declare (xargs :guard t))
  (cond ((atom alist) (eq alist nil))
        (t (and (consp (car alist))
                (symbolp (car (car alist)))
                (consp (cdr (car alist)))
                (symbolp (cadr (car alist)))
                (natp (cddr (car alist)))
                (hit-count-info-worldp (cdr alist))))))

;limit?
(local
  (defthm plist-worldp-when-hit-count-info-worldp
    (implies (hit-count-info-worldp alist)
             (plist-worldp alist))
    :hints (("Goal" :in-theory (enable hit-count-info-worldp plist-worldp)))))

(local
  (defthm natp-of-getprop-when-hit-count-info-worldp
    (implies (and (hit-count-info-worldp hit-counts)
                  (natp val))
             (natp (sgetprop rule-symbol key val world-name hit-counts)))
    :hints (("Goal" :in-theory (enable hit-count-info-worldp)))))

(local
  (defthm hit-count-info-worldp-of-uniquify-alist-eq-aux
    (implies (and (hit-count-info-worldp hit-counts)
                  (hit-count-info-worldp acc))
             (hit-count-info-worldp (uniquify-alist-eq-aux hit-counts acc)))
    :hints (("Goal" :in-theory (enable hit-count-info-worldp acons)))))

(local
  (defthmd symbol-alistp-when-hit-count-info-worldp
    (implies (hit-count-info-worldp hit-counts)
             (symbol-alistp hit-counts))
    :hints (("Goal" :in-theory (enable hit-count-info-worldp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Either nil (not counting hits), or a natp (total number of rule hits, not
;; split out by rule), or a hit-count-info-worldp that assigns hit counts to
;; individual rules.
(defund hit-countsp (hit-counts)
  (declare (xargs :guard t))
  (or (null hit-counts)
      (natp hit-counts)
      (hit-count-info-worldp hit-counts)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Consider not calling extend-world each time (instead, maybe try every 20 times).
(defund increment-hit-count (rule-symbol hit-counts)
  (declare (xargs :guard (and (symbolp rule-symbol)
                              (hit-count-info-worldp hit-counts))))
    (let* ((count (the (integer 0 *) (getprop rule-symbol 'hit-count 0 'hit-counts hit-counts)))
           (count (the (integer 0 *) (+ 1 count)))
           (hit-counts (extend-world 'hit-counts (putprop rule-symbol 'hit-count count hit-counts))))
      hit-counts))

(local
  (defthm hit-count-info-worldp-of-increment-hit-count
    (implies (and (hit-count-info-worldp hit-counts)
                  (symbolp rule-symbol))
             (hit-count-info-worldp (increment-hit-count rule-symbol hit-counts)))
    :hints (("Goal" :in-theory (enable increment-hit-count hit-count-info-worldp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;rename
;; We inline this to optimize the case when hit-counts is nil.
;; We keep this disabled to avoid case splits in proofs about code that calls it.
(defund-inline maybe-increment-hit-count (rule-symbol hit-counts)
  (declare (xargs :guard (and (symbolp rule-symbol)
                              (hit-countsp hit-counts) ; allows nil, meaning no hit-counts
                              )
                  :guard-hints (("Goal" :in-theory (enable hit-countsp)))))
  ;; if hit-counts is nil, it remains so:
  (and hit-counts
       (if (natp hit-counts)
           (+ 1 hit-counts)
         (increment-hit-count rule-symbol hit-counts))))

(defthm hit-countsp-of-maybe-increment-hit-count
  (implies (and (hit-countsp hit-counts)
                (symbolp rule-symbol))
           (hit-countsp (maybe-increment-hit-count rule-symbol hit-counts)))
  :hints (("Goal" :in-theory (enable maybe-increment-hit-count hit-countsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; not counting hits at all
(defund no-hit-counting ()
  (declare (xargs :guard t))
  nil)

;; Disabled since this is a ground term
(defthmd hit-countsp-of-no-hit-counting
  (hit-countsp (no-hit-counting)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Initially 0, ready to increment.
(defund zero-hits ()
  (declare (xargs :guard t))
  0)

;; Disabled since this is a ground term
(defthmd hit-countsp-of-zero-hits
  (hit-countsp (zero-hits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Empty so far, but being extended.
(defund empty-hit-counts ()
  (declare (xargs :guard t))
  (prog2$ (retract-world 'hit-counts nil)
          ;setting :fake means that hit-counts is nil iff we are not tracking the hit-counts
          (increment-hit-count :fake nil)))

;; Disabled since this is a ground term
(defthmd hit-countsp-of-empty-hit-counts
  (hit-countsp (empty-hit-counts)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Simpler structures used for printing or comparing hit-counts.
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
    :hints (("Goal" :in-theory (enable all-cdrs-rationalp hit-count-alistp)))))

(local
  (defthmd natp-of-lookup-equal-when-hit-count-alistp
    (implies (hit-count-alistp alist)
             (or (natp (lookup-equal sym alist))
                 (not (lookup-equal sym alist))))
    :rule-classes :type-prescription
    :otf-flg t ; why?
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
  (declare (xargs :guard (and (hit-count-info-worldp hit-counts)
                              (alistp acc))
                  :guard-hints (("Goal" :in-theory (enable hit-count-info-worldp)))))
  (if (endp hit-counts)
      acc
    (let* ((entry (car hit-counts))
           (symbol (car entry))
           ;;(key (cadr entry)) ;should be 'hit-count
           (hit-count (cddr entry)))
      (make-hit-count-alist-aux (cdr hit-counts) (if (eq :fake symbol) acc (acons-fast symbol hit-count acc))))))

(local
  (defthm hit-count-alistp-of-make-hit-count-alist-aux
    (implies (and (hit-count-info-worldp hit-counts)
                  (hit-count-alistp acc))
             (hit-count-alistp (make-hit-count-alist-aux hit-counts acc)))
    :hints (("Goal" :in-theory (enable hit-count-alistp symbol-alistp strip-cdrs hit-count-info-worldp
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
;;     (implies (and (hit-count-info-worldp hit-counts)
;;                   (all-cdrs-rationalp acc))
;;              (all-cdrs-rationalp (make-hit-count-alist-aux hit-counts acc)))
;;     :hints (("Goal" :in-theory (enable hit-count-info-worldp make-hit-count-alist-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This gets rid of the mention of :fake.
(defund make-hit-count-alist (hit-counts)
  (declare (xargs :guard (hit-count-info-worldp hit-counts)))
  (make-hit-count-alist-aux (uniquify-alist-eq hit-counts) nil))

(defthm hit-count-alistp-of-make-hit-count-alist
  (implies (hit-count-info-worldp hit-counts)
           (hit-count-alistp (make-hit-count-alist hit-counts)))
  :hints (("Goal" :in-theory (enable make-hit-count-alist))))

;; ;; todo: do we need all these type rules?

;; ;; (defthm all-consp-of-make-hit-count-alist
;; ;;   (all-consp (make-hit-count-alist hit-counts))
;; ;;   :hints (("Goal" :in-theory (enable make-hit-count-alist))))

;; ;; (defthm true-listp-of-make-hit-count-alist
;; ;;   (true-listp (make-hit-count-alist hit-counts))
;; ;;   :hints (("Goal" :in-theory (enable make-hit-count-alist))))

;; ;; (defthm alistp-of-make-hit-count-alist
;; ;;   (alistp (make-hit-count-alist hit-counts))
;; ;;   :hints (("Goal" :in-theory (enable make-hit-count-alist))))

;; ;; (defthm all-cdrs-rationalp-of-make-hit-count-alist
;; ;;   (implies (hit-countsp hit-counts)
;; ;;            (all-cdrs-rationalp (make-hit-count-alist hit-counts)))
;; ;;   :hints (("Goal" :in-theory (enable hit-countsp make-hit-count-alist))))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund sort-hit-count-alist (alist)
  (declare (xargs :guard (hit-count-alistp alist)))
  (merge-sort-by-cdr-> alist))

(defthm hit-count-alistp-of-sort-hit-count-alist
  (implies (hit-count-alistp alist)
           (hit-count-alistp (sort-hit-count-alist alist)))
  :hints (("Goal" :in-theory (enable hit-count-alistp sort-hit-count-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; the alist should have shadowed paris already removed
(defund add-counts-in-hit-count-alist (alist acc)
  (declare (xargs :guard (and (hit-count-alistp alist)
                              (natp acc))
                  :guard-hints (("Goal" :in-theory (enable hit-count-alistp)))))
  (if (endp alist)
      acc
    (let* ((pair (first alist))
           (count (cdr pair)))
      (add-counts-in-hit-count-alist (rest alist) (+ count acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Consider optimizing this by looping through all the rule names and
;; just looking up their counts, instead of calling uniquify-alist-eq.
;; Returns a hit-count-alist mapping rule names to hit counts.
(defund summarize-hit-counts (hit-counts)
  (declare (xargs :guard (hit-count-info-worldp hit-counts)))
  (let* (; (hit-counts (uniquify-alist-eq hit-counts)) ;does this not use the fast lookup into the hit-counts?
         (hit-count-alist (make-hit-count-alist hit-counts))
         ) ;removes shadowed bindings
    (sort-hit-count-alist hit-count-alist)))

(local
  (defthm hit-count-alistp-of-summarize-hit-counts
    (implies (hit-count-info-worldp hit-counts)
             (hit-count-alistp (summarize-hit-counts hit-counts)))
    :hints (("Goal" :in-theory (enable summarize-hit-counts
                                       hit-count-info-worldp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We print the hit-counts, to whatever level of detail they contain
(defund maybe-print-hit-counts (hit-counts)
  (declare (xargs :guard (hit-countsp hit-counts)
                  :guard-hints (("Goal" :in-theory (enable hit-countsp)))))
  (if (equal hit-counts (no-hit-counting))
      nil ;; We are not counting hits, so do nothing
    (if (natp hit-counts)
        ;; just counting the total number of hits:
        (if (= (zero-hits) hit-counts)
            (cw "(No hits.)")
          (if (eql 1 hit-counts)
              (cw "(1 hit.)")
            (cw "(~x0 hits.)" hit-counts)))
      ;; Print the rules and their hit counts:
      (let* ((sorted-hit-count-alist (summarize-hit-counts hit-counts))
             (num-hits (add-counts-in-hit-count-alist sorted-hit-count-alist 0)))
        (progn$ (if (= 0 num-hits)
                    (cw "(No hits.)")
                  (if (eql 1 num-hits)
                      (cw "(1 hit:~%~y0)" sorted-hit-count-alist)
                    (cw "(~x0 hits:~%~y1)" num-hits sorted-hit-count-alist)))
                ;;todo: put this back but make it a separate option, off by default:
                ;; (let* ((useful-rules (strip-cars rule-count-alist))
                ;;        (useless-rules (set-difference-eq all-rule-names useful-rules)))
                ;;   (cw "(~x0 Useless rules: ~x1.)~%" (len useless-rules) useless-rules)
                ;;   )
                )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; Make a hit count alist where each rule's count is its count in alist1 minus
;; ;; its count in alist2.  We expect alist1 to be an "superset" (in the sense of
;; ;; each rule having at least as many hits) of alist2, so the subtractions will
;; ;; never give negative numbers, but we just call nfix to enforce that.
;; (defund subtract-hit-count-alists (alist1 alist2)
;;   (declare (xargs :guard (and (hit-count-alistp alist1)
;;                               (hit-count-alistp alist2))
;;                   :guard-hints (("Goal" :in-theory (enable HIT-COUNT-ALISTP)))
;;                   :verify-guards nil ;; done below
;;                   ))
;;   (if (endp alist1)
;;       nil
;;     (let* ((entry (car alist1))
;;            (sym (car entry))
;;            (count (cdr entry))
;;            (maybe-other-count (lookup-eq sym alist2))
;;            (other-count (if maybe-other-count maybe-other-count 0))
;;            (count-diff (nfix (- count other-count))) ;we don't let it go negative
;;            )
;;       (if (posp count-diff)
;;           (acons sym count-diff (subtract-hit-count-alists (rest alist1) alist2))
;;         ;; skip things with 0 count:
;;         (subtract-hit-count-alists (rest alist1) alist2)))))

;; (defthm hit-count-alistp-of-subtract-hit-count-alists
;;   (implies (and (hit-count-alistp alist1)
;;                 (hit-count-alistp alist2))
;;            (hit-count-alistp (subtract-hit-count-alists alist1 alist2)))
;;   :hints (("Goal" :in-theory (enable hit-count-alistp subtract-hit-count-alists))))

;; ;; (local
;; ;;   (defthm alistp-of-subtract-hit-count-alists
;; ;;     (alistp (subtract-hit-count-alists alist1 alist2))
;; ;;     :hints (("Goal" :in-theory (enable hit-count-alistp subtract-hit-count-alists)))))

;; (verify-guards subtract-hit-count-alists
;;   :hints (("Goal" :in-theory (enable nat-of-cdr-of-car-when-hit-count-alistp
;;                                      natp-of-lookup-equal-when-hit-count-alistp))))

;; ;; (local
;; ;;   (defthm all-cdrs-rationalp-of-subtract-hit-count-alists
;; ;;     (implies (and (hit-count-alistp alist1)
;; ;;                   (hit-count-alistp alist2))
;; ;;              (all-cdrs-rationalp (subtract-hit-count-alists alist1 alist2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund count-hits-argp (count-hits)
  (declare (xargs :guard t))
  (member-eq count-hits '(t nil :total)))

(defund initialize-hit-counts (count-hits)
  (declare (xargs :guard (count-hits-argp count-hits)))
  (if (eq t count-hits)
      (empty-hit-counts) ; count hits for each rule
    (if (eq :total count-hits)
        (zero-hits)
      ;; must be nil:
      (no-hit-counting))))

(defthm hit-countsp-of-initialize-hit-counts
  (hit-countsp (initialize-hit-counts arga))
  :hints (("Goal" :in-theory (enable initialize-hit-counts))))
