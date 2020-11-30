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
(include-book "kestrel/utilities/acons-fast" :dir :system)
(include-book "merge-sort-by-cdr-greater")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

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
                (rationalp (cddr (car alist))) ;new (could require natp)
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
  :hints (("Goal" :in-theory (enable INFO-WORLDP))))

(defthm info-worldp-of-uniquify-alist-eq-aux
  (implies (and (info-worldp info)
                (info-worldp acc))
           (info-worldp (uniquify-alist-eq-aux info acc)))
  :hints (("Goal" :in-theory (enable info-worldp acons))))

(defthm symbol-alistp-when-info-worldp
  (implies (info-worldp info)
           (symbol-alistp info))
  :hints (("Goal" :in-theory (enable info-worldp))))

;; TODO: Consider optimizing this by looping through all the rule names and
;; just looking up their counts, instead of calling uniquify-alist-eq.
;; Returns an alist.
(defund summarize-info-world (info)
  (declare (xargs :guard (info-worldp info)))
  (let* ((info (uniquify-alist-eq info)) ;does this not use the fast lookup into the info?
         (hit-count-alist (make-hit-count-alist info nil))
         ) ;removes shadowed bindings
    (merge-sort-by-cdr-> hit-count-alist)))

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
