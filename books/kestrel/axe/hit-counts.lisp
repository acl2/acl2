; Counting how many times rewrite rules apply
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: See also count-worlds.lisp.  Can we just use that machinery?
;; TODO: Or generalize this machinery to count things other than counts, eg.,
;; useful and useles tries.

(include-book "all-consp")
(include-book "kestrel/alists-light/uniquify-alist-eq" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/utilities/acons-fast" :dir :system)
(include-book "merge-sort-by-cdr-greater")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(defthm symbol-alistp-of-evens
  (implies (symbol-alistp alist)
           (symbol-alistp (evens alist)))
  :hints (("Goal" :induct t
           :in-theory (enable symbol-alistp evens))))

(defthm symbol-alistp-of-odds
  (implies (symbol-alistp alist)
           (symbol-alistp (odds alist)))
  :hints (("Goal" :induct t
           :in-theory (enable symbol-alistp odds))))

(defthm symbol-alistp-of-merge-by-cdr->
  (implies (and (symbol-alistp l1)
                (symbol-alistp l2)
                (symbol-alistp acc))
           (symbol-alistp (merge-by-cdr-> l1 l2 acc)))
  :hints (("Goal" :in-theory (enable merge-by-cdr->))))

(defthm symbol-alistp-of-merge-sort-by-cdr->
  (implies (symbol-alistp alist)
           (symbol-alistp (merge-sort-by-cdr-> alist)))
  :hints (("Goal" :in-theory (enable merge-sort-by-cdr->))))

(defthm nat-listp-of-strip-cdrs-of-evens
  (implies (nat-listp (strip-cdrs alist))
           (nat-listp (strip-cdrs (evens alist))))
  :hints (("Goal" :induct t
           :in-theory (enable nat-listp evens))))

(defthm nat-listp-of-strip-cdrs-of-odds
  (implies (nat-listp (strip-cdrs alist))
           (nat-listp (strip-cdrs (odds alist))))
  :hints (("Goal" :induct t
           :in-theory (enable nat-listp odds))))

(defthm nat-listp-of-strip-cdrs-of-merge-by-cdr->
  (implies (and (nat-listp (strip-cdrs l1))
                (nat-listp (strip-cdrs l2))
                (nat-listp (strip-cdrs acc)))
           (nat-listp (strip-cdrs (merge-by-cdr-> l1 l2 acc))))
  :hints (("Goal" :in-theory (enable merge-by-cdr->))))

(defthm nat-listp-of-strip-cdrs-of-merge-sort-by-cdr->
  (implies (nat-listp (strip-cdrs alist))
           (nat-listp (strip-cdrs (merge-sort-by-cdr-> alist))))
  :hints (("Goal" :in-theory (enable merge-sort-by-cdr->))))



;;
;; counting rule uses (using a custom world)
;;

;; A true-list of triples of the form (sym prop . val).  See :doc world.  A
;; specialization of plist-worldp that requires the values to be rationals.
;; Note that nil satisfies info-worldp but means that we are not counting hits
;; at all (see empty-info-world).  So we could call this maybe-info-worldp.
(defund info-worldp (alist)
  (declare (xargs :guard t))
  (cond ((atom alist) (eq alist nil))
        (t (and (consp (car alist))
                (symbolp (car (car alist)))
                (consp (cdr (car alist)))
                (symbolp (cadr (car alist)))
                (natp (cddr (car alist)))
                (info-worldp (cdr alist))))))

;limit?
(defthm worldp-when-info-plist-worldp
  (implies (info-worldp alist)
           (plist-worldp alist))
  :hints (("Goal" :in-theory (enable info-worldp plist-worldp))))

(defthm acl2-numberp-of-getprop-when-info-worldp
  (implies (and (info-worldp info)
                (acl2-numberp val))
           (acl2-numberp (sgetprop rule-symbol key val world-name info)))
  :hints (("Goal" :in-theory (enable info-worldp))))

(defthm rationalp-of-getprop-when-info-worldp
  (implies (and (info-worldp info)
                (rationalp val))
           (rationalp (sgetprop rule-symbol key val world-name info)))
  :hints (("Goal" :in-theory (enable info-worldp))))

;; TODO: Consider not calling extend-world each time (instead, maybe try every 20 times).
(defund increment-hit-count-in-info-world (rule-symbol info)
  (declare (xargs :guard (and (symbolp rule-symbol)
                              (info-worldp info))))
    (let* ((count (getprop rule-symbol 'hit-count 0 'info-world info))
           (count (+ 1 count))
           (info (extend-world 'info-world (putprop rule-symbol 'hit-count count info))))
      info))

(defthm info-worldp-of-increment-hit-count-in-info-world
  (implies (and (info-worldp info)
                (symbolp rule-symbol))
           (info-worldp (increment-hit-count-in-info-world rule-symbol info)))
  :hints (("Goal" :in-theory (enable increment-hit-count-in-info-world info-worldp))))

(defun empty-info-world ()
  (declare (xargs :guard t))
  (prog2$ (retract-world 'info-world nil)
          ;setting :fake means that info is nil iff we are not tracking the info
          (increment-hit-count-in-info-world :fake nil)))

;; Disabled since this is a ground term
(defthmd info-worldp-of-empty-info-world
  (info-worldp (empty-info-world)))

(defund hit-count-alistp (alist)
  (declare (xargs :guard t))
  (and (symbol-alistp alist)
       (nat-listp (strip-cdrs alist))))

(defthm hit-count-alistp-forward-to-symbol-alistp
  (implies (hit-count-alistp alist)
           (symbol-alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable hit-count-alistp))))

(defthm hit-count-alistp-of-cdr
  (implies (hit-count-alistp alist)
           (hit-count-alistp (cdr alist)))
  :hints (("Goal" :in-theory (enable hit-count-alistp))))

(defthm hit-count-alistp-forward-to-all-consp
  (implies (hit-count-alistp alist)
           (all-consp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable hit-count-alistp))))

(defthm all-cdrs-rationalp-when-hit-count-alistp
  (implies (hit-count-alistp alist)
           (all-cdrs-rationalp alist))
  :hints (("Goal" :in-theory (enable hit-count-alistp))))

(defthmd natp-of-lookup-equal-when-hit-count-alistp
  (implies (hit-count-alistp alist)
           (or (natp (lookup-equal sym alist))
               (not (lookup-equal sym alist))))
  :rule-classes :type-prescription
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (hit-count-alistp lookup-equal assoc-equal STRIP-CDRS) (CDR-IFF)))))

(defthmd nat-of-cdr-of-car-when-hit-count-alistp
  (implies (and (hit-count-alistp alist)
                (consp alist))
           (natp (cdr (car alist))))
  :rule-classes :type-prescription
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (hit-count-alistp lookup-equal assoc-equal STRIP-CDRS) (CDR-IFF)))))

(defthmd consp-car-when-hit-count-alistp
  (implies (and (hit-count-alistp alist)
                (consp alist))
           (consp (car alist)))
  :rule-classes :type-prescription
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (hit-count-alistp lookup-equal assoc-equal STRIP-CDRS) (CDR-IFF)))))

;; The info should be uniquify-ed before calling this.
;; This gets rid of the mention of :fake.
(defun make-hit-count-alist (info acc)
  (declare (xargs :guard (and (info-worldp info)
                              (alistp acc))
                  :guard-hints (("Goal" :in-theory (enable info-worldp)))))
  (if (endp info)
      acc
    (let* ((entry (car info))
           (symbol (car entry))
           ;;(key (cadr entry)) ;should be 'hit-count
           (hit-count (cddr entry)))
      (make-hit-count-alist (cdr info) (if (eq :fake symbol) acc (acons-fast symbol hit-count acc))))))

(defthm hit-count-alistp-of-make-hit-count-alist
  (implies (and (info-worldp info)
                (hit-count-alistp acc))
           (hit-count-alistp (make-hit-count-alist info acc)))
  :hints (("Goal" :in-theory (enable hit-count-alistp SYMBOL-ALISTP strip-cdrs INFO-WORLDP))))

(defthm all-consp-of-make-hit-count-alist
  (implies (all-consp acc)
           (all-consp (make-hit-count-alist info acc))))

(defthm true-listp-of-make-hit-count-alist
  (implies (true-listp acc)
           (true-listp (make-hit-count-alist info acc))))

(defthm alistp-of-make-hit-count-alist
  (implies (alistp acc)
           (alistp (make-hit-count-alist info acc))))

(defthm all-cdrs-rationalp-of-make-hit-count-alist
  (implies (and (info-worldp info)
                (all-cdrs-rationalp acc))
           (all-cdrs-rationalp (make-hit-count-alist info acc)))
  :hints (("Goal" :in-theory (enable info-worldp))))

(defthm info-worldp-of-uniquify-alist-eq-aux
  (implies (and (info-worldp info)
                (info-worldp acc))
           (info-worldp (uniquify-alist-eq-aux info acc)))
  :hints (("Goal" :in-theory (enable info-worldp acons))))

(defthm symbol-alistp-when-info-worldp
  (implies (info-worldp info)
           (symbol-alistp info))
  :hints (("Goal" :in-theory (enable info-worldp))))

(defund sort-hit-count-alist (alist)
  (declare (xargs :guard (hit-count-alistp alist)))
  (merge-sort-by-cdr-> alist))

(defthm hit-count-alistp-of-sort-hit-count-alist
  (implies (hit-count-alistp alist)
           (hit-count-alistp (sort-hit-count-alist alist)))
  :hints (("Goal" :in-theory (enable hit-count-alistp sort-hit-count-alist))))


;; TODO: Consider optimizing this by looping through all the rule names and
;; just looking up their counts, instead of calling uniquify-alist-eq.
;; Returns a hit-count-alist mapping rule names to hit counts.
(defund summarize-info-world (info)
  (declare (xargs :guard (info-worldp info)))
  (let* ((info (uniquify-alist-eq info)) ;does this not use the fast lookup into the info?
         (hit-count-alist (make-hit-count-alist info nil))
         ) ;removes shadowed bindings
    (sort-hit-count-alist hit-count-alist)))

(defthm alistp-of-summarize-info-world
  (implies (info-worldp info)
           (alistp (summarize-info-world info)))
  :hints (("Goal" :in-theory (enable summarize-info-world
                                     info-worldp))))

;better message if no hits?
;use this more?
(defun print-hit-counts (print info all-rule-names)
  (declare (xargs :guard (and (info-worldp info)
                              (symbol-listp all-rule-names))))
  (let ((len (len info)))
    ;; TODO: We are transitioning to not counting hits for :brief printing
    (if (eq :brief print)
        ;; Just print the number of hits (TODO: In this case, we could keep a simple count of hits, rather than counting the hits of each rule):
        (if (= 0 len)
            (cw "(No hits.)")
          (if (eql 1 len)
              (cw "(1 hit.)")
            (cw "(~x0 hits.)" len)))
      ;; Print the rules and their hit counts, and print the useless rules:
      (let ((rule-count-alist (summarize-info-world info)))
        (prog2$ (if (= 0 len)
                    (cw "(No hits.)")
                  (if (eql 1 len)
                      (cw "(1 hit:~%~y0)" rule-count-alist)
                    (cw "(~x0 hits:~%~y1)" len rule-count-alist)))
                (let* ((useful-rules (strip-cars rule-count-alist))
                       (useless-rules (set-difference-eq all-rule-names useful-rules)))
                  (cw "(~x0 Useless rules: ~x1.)~%" (len useless-rules) useless-rules)))))))

;; Make a hit count alist where each rule's count is its count in alist1 minus
;; its count in alist2.  We expect alist1 to be an "superset" (in the sense of
;; each rule having at least as many hits) of alist2, so the subtractions will
;; never give negative numbers, but we just call nfix to enforce that.
(defun subtract-hit-count-alists (alist1 alist2)
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

(defthm alistp-of-subtract-hit-count-alists
  (implies (and (hit-count-alistp alist1)
                (hit-count-alistp alist2))
           (alistp (subtract-hit-count-alists alist1 alist2)))
  :hints (("Goal" :in-theory (enable hit-count-alistp subtract-hit-count-alists))))

(verify-guards subtract-hit-count-alists
  :hints (("Goal" :in-theory (enable nat-of-cdr-of-car-when-hit-count-alistp
                                     natp-of-lookup-equal-when-hit-count-alistp))))

(defthm all-cdrs-rationalp-of-subtract-hit-count-alists
  (implies (and (hit-count-alistp alist1)
                (hit-count-alistp alist2))
           (all-cdrs-rationalp (subtract-hit-count-alists alist1 alist2))))
