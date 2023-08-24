; Recommendations used to express proof advice
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HELP")

(include-book "kestrel/alists-light/lookup-equal-def" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-def" :dir :system)
(include-book "kestrel/utilities/widen-margins" :dir :system)
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system)) ; for acl2::consp-of-car-when-alistp-cheap
(local (include-book "kestrel/alists-light/lookup-eq" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))

#+:non-standard-analysis
(local (defthm realp-when-rationalp (implies (rationalp x) (acl2::realp x))))

(defconst *rec-to-symbol-alist*
  '(;; For these, training data is obtained by removing the entire "hint
    ;; setting" (e.g., the entire ":by XXX"):
    ("add-by-hint" . :add-by-hint) ; rare
    ("add-cases-hint" . :add-cases-hint) ; rare
    ("add-induct-hint" . :add-induct-hint)
    ("add-nonlinearp-hint" . :add-nonlinearp-hint) ; very rare

    ;; For these, gathering training data always involves removing individual
    ;; items to :use or :expand:
    ("add-expand-hint" . :add-expand-hint)
    ("add-use-hint" . :add-use-hint)

    ;; For :in-theory, gathering training data involves either removing
    ;; individual items to enable or disable (when the :in-theory is an enable,
    ;; disable, or e/d), or else removing the whole :in-theory:
    ("add-disable-hint" . :add-disable-hint)
    ("add-enable-hint" . :add-enable-hint)

    ;; For :do-not, gathering training data involves either removing individual
    ;; items (if the :do-not is given a quoted list of symbols), or else
    ;; removing the whole :do-not:
    ("add-do-not-hint" . :add-do-not-hint)

    ;; Confusingly named: Does not indicate a :use hint and the "lemma" is
    ;; often a defun.  Gathering training data involves artificially "knocking
    ;; out" rules used in a successful proof.  This is often treated like
    ;; add-enable-hint.
    ("use-lemma" . :use-lemma)

    ;; Gathering training data involves artificially "knocking out" supporting
    ;; books used in a successful proof.
    ("add-library" . :add-library)

    ("add-hyp" . :add-hyp) ; can change the meaning of the theorem!

    ("exact-hints" . :exact-hints)))

(defconst *rec-types* (strip-cdrs *rec-to-symbol-alist*))

(defund rec-typep (type)
  (declare (xargs :guard t))
  (member-eq type *rec-types*))

(defthm rec-typep-forward-to-symbolp
  (implies (rec-typep type)
           (symbolp type))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rec-typep member-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: include in a recommendation
;; todo: rename to pre-events?
(defund pre-commandsp (pre-commands)
  (declare (xargs :guard t))
  (true-listp pre-commands))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund include-book-formp (form)
  (declare (xargs :guard t))
  (and (consp form)
       (true-listp form)
       (eq 'include-book (car form))
       (stringp (cadr form))
       ;; todo: what else?
       ))

(defund include-book-form-listp (forms)
  (declare (xargs :guard t))
  (if (atom forms)
      (null forms)
    (and (include-book-formp (first forms))
         (include-book-form-listp (rest forms)))))

(local
 (defthm include-book-form-listp-forward-to-true-listp
   (implies (include-book-form-listp forms)
            (true-listp forms))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable include-book-form-listp)))))

(defthm include-book-form-listp-of-union-equal
  (implies (and (include-book-form-listp info1)
                (include-book-form-listp info2))
           (include-book-form-listp (union-equal info1 info2)))
  :hints (("Goal" :in-theory (enable include-book-form-listp union-equal))))

(defund include-book-infop (info)
  (declare (xargs :guard t))
  (or (eq :builtin info)
      (include-book-form-listp info)))

(local
 (defthm true-listp-when-include-book-infop
   (implies (include-book-infop info)
            (equal (true-listp info)
                   (not (equal :builtin info))))
   :hints (("Goal" :in-theory (enable include-book-infop)))))

;; for now, if one is :builtin, we just take the other (but should that ever happen?)
(defund combine-include-book-infos (info1 info2)
  (declare (xargs :guard (and (include-book-infop info1)
                              (include-book-infop info2))))
  (if (eq :builtin info1)
      info2
    (if (eq :builtin info2)
        info1
      (union-equal info1 info2))))

(local
 (defthm include-book-infop-of-combine-include-book-infos
   (implies (and (include-book-infop info1)
                 (include-book-infop info2))
            (include-book-infop (combine-include-book-infos info1 info2)))
   :hints (("Goal" :in-theory (enable include-book-infop
                                      combine-include-book-infos)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund include-book-info-listp (infos)
  (declare (xargs :guard t))
  (if (atom infos)
      (null infos)
    (and (include-book-infop (first infos))
         (include-book-info-listp (rest infos)))))

(local
 (defthm include-book-info-listp-forward-to-true-listp
   (implies (include-book-info-listp infos)
            (true-listp infos))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable include-book-info-listp)))))

(defthm include-book-info-listp-of-take
  (implies (include-book-info-listp infos)
           (include-book-info-listp (take n infos)))
  :hints (("Goal" :in-theory (enable include-book-info-listp take))))

(defthm include-book-info-listp-of-revappend
  (implies (and (include-book-info-listp rec-lists1)
                (include-book-info-listp rec-lists2))
           (include-book-info-listp (revappend rec-lists1 rec-lists2)))
  :hints (("Goal" :in-theory (enable include-book-info-listp revappend))))

(defthm include-book-info-listp-of-reverse
  (implies (include-book-info-listp rec-lists)
           (include-book-info-listp (reverse rec-lists)))
  :hints (("Goal" :in-theory (enable reverse))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund book-mapp (book-map)
  (declare (xargs :guard t))
  (and (symbol-alistp book-map)
       (include-book-info-listp (strip-cdrs book-map))))

(local
 (defthm book-mapp-forward-to-alistp
   (implies (book-mapp book-map)
            (alistp book-map))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable book-mapp)))))

(local
 (defthm book-mapp-forward-to-symbol-alistp
   (implies (book-mapp book-map)
            (symbol-alistp book-map))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable book-mapp)))))

(defthm book-mapp-of-pairlis$
  (implies (and (symbol-listp keys)
                (include-book-info-listp vals))
           (book-mapp (pairlis$ keys vals)))
  :hints (("Goal" :in-theory (enable book-mapp include-book-info-listp))))

(local
 (defthm include-book-infop-of-lookup-equal
   (implies (book-mapp book-map)
            (include-book-infop (acl2::lookup-equal key book-map)))
   :hints (("Goal" :in-theory (enable book-mapp acl2::lookup-equal assoc-equal include-book-info-listp)))))

(local
 (defthm symbol-listp-of-strip-cars-when-book-mapp
   (implies (book-mapp book-map)
            (symbol-listp (strip-cars book-map)))
   :hints (("Goal" :in-theory (enable book-mapp)))))

(defund combine-book-maps-aux (keys map1 map2 acc)
  (declare (xargs :guard (and (symbol-listp keys)
                              (book-mapp map1)
                              (book-mapp map2)
                              (alistp acc))))
  (if (endp keys)
      acc
    (let* ((key (first keys))
           (info1 (acl2::lookup-eq key map1))
           (info2 (acl2::lookup-eq key map2))
           (val (if (not info1)
                    info2
                  (if (not info2)
                      info1
                    (combine-include-book-infos info1 info2)))))
      (combine-book-maps-aux (rest keys) map1 map2
                             (acons key
                                    val
                                    acc)))))

(local
 (defthm book-mapp-of-combine-book-maps-aux
   (implies (and (symbol-listp keys)
                 (book-mapp map1)
                 (book-mapp map2)
                 (book-mapp acc))
            (book-mapp (combine-book-maps-aux keys map1 map2 acc)))
   :hints (("Goal"
            :in-theory (enable combine-book-maps-aux
                               book-mapp
                               include-book-info-listp)))))

(defund combine-book-maps (map1 map2)
  (declare (xargs :guard (and (book-mapp map1)
                              (book-mapp map2))))
  (combine-book-maps-aux (union-eq (strip-cars map1) (strip-cars map2))
                         map1
                         map2
                         nil))

(defthm book-mapp-of-combine-book-maps
  (implies (and (book-mapp map1)
                (book-mapp map2))
           (book-mapp (combine-book-maps map1 map2)))
  :hints (("Goal" :in-theory (enable combine-book-maps))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund confidence-percentp (p)
  (declare (xargs :guard t))
  (and (rationalp p)
       (<= 0 p)
       (<= p 100)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes a well-formed recommendation (coming from one of the models).
;; todo: strengthen
(defund recommendationp (rec)
  (declare (xargs :guard t))
  (and (true-listp rec)
       (= 5 (len rec))
       (let ((name (nth 0 rec))
             (type (nth 1 rec)) ; action type
             ;; (object (nth 2 rec)) ; action object
             (confidence-percent (nth 3 rec))
             (book-map (nth 4 rec)) ; maps symbols to books that may define them
             )
         (and (stringp name)
              (rec-typep type)
              ;; object
              (confidence-percentp confidence-percent)
              (book-mapp book-map)))))

(defthm recommendationp-forward-to-true-listp
  (implies (recommendationp rec)
           (true-listp rec))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable recommendationp))))

(defthmd true-listp-when-recommendationp
  (implies (recommendationp rec)
           (true-listp rec))
  :hints (("Goal" :in-theory (enable recommendationp))))
(local (in-theory (enable true-listp-when-recommendationp)))

;; Disabled since hung on common function stringp
(defthmd stringp-of-nth-0-when-recommendationp
  (implies (recommendationp rec)
           (stringp (nth 0 rec)))
  :hints (("Goal" :in-theory (enable recommendationp))))
(local (in-theory (enable stringp-of-nth-0-when-recommendationp)))

(defthm rec-typep-of-nth-1-when-recommendationp
  (implies (recommendationp rec)
           (rec-typep (nth 1 rec)))
  :hints (("Goal" :in-theory (enable recommendationp))))

;; Disabled since hung on common function rationalp
(defthmd rationalp-of-nth-3-when-recommendationp
  (implies (recommendationp rec)
           (rationalp (nth 3 rec)))
  :hints (("Goal" :in-theory (enable recommendationp))))
(local (in-theory (enable rationalp-of-nth-3-when-recommendationp)))

(defthm confidence-percentp-of-nth-3-when-recommendationp
  (implies (recommendationp rec)
           (confidence-percentp (nth 3 rec)))
  :hints (("Goal" :in-theory (enable recommendationp))))

(defthm book-mapp-of-nth-4-when-recommendationp
  (implies (recommendationp rec)
           (book-mapp (nth 4 rec)))
  :hints (("Goal" :in-theory (enable recommendationp))))

;; (local
;;  (defthm true-listp-of-nth-6-when-recommendationp
;;    (implies (recommendationp rec)
;;             (true-listp (nth 6 rec)))
;;    :hints (("Goal" :in-theory (enable recommendationp)))))

;; (local
;;  (defthm rec-sourcesp-of-nth-6-when-recommendationp
;;    (implies (recommendationp rec)
;;             (rec-sourcesp (nth 6 rec)))
;;    :hints (("Goal" :in-theory (enable recommendationp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund make-rec (name type object confidence-percent book-map)
  (declare (xargs :guard (and (stringp name)
                              (rec-typep type)
                              ;; object
                              (confidence-percentp confidence-percent)
                              (book-mapp book-map))))
  (list name type object confidence-percent book-map))

(defthm recommendationp-of-make-rec
  (equal (recommendationp (make-rec name type object confidence-percent book-map))
         (and (stringp name)
              (rec-typep type)
              ;; object
              (confidence-percentp confidence-percent)
              (book-mapp book-map)))
  :hints (("Goal" :in-theory (enable make-rec recommendationp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund recommendation-listp (recs)
  (declare (xargs :guard t))
  (if (atom recs)
      (null recs)
    (and (recommendationp (first recs))
         (recommendation-listp (rest recs)))))

(defthm recommendation-listp-forward-to-true-listp
  (implies (recommendation-listp recs)
           (true-listp recs))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable recommendation-listp))))

(defthm recommendation-listp-of-remove-equal
  (implies (recommendation-listp recs)
           (recommendation-listp (remove-equal rec recs)))
  :hints (("Goal" :in-theory (enable recommendation-listp))))

(defthm recommendation-listp-of-revappend
  (implies (and (recommendation-listp recs1)
                (recommendation-listp recs2))
           (recommendation-listp (revappend recs1 recs2)))
  :hints (("Goal" :in-theory (enable recommendation-listp revappend))))

(defthm recommendation-listp-of-reverse
  (implies (recommendation-listp recs)
           (recommendation-listp (reverse recs)))
  :hints (("Goal" :in-theory (enable recommendation-listp reverse))))

(defthm recommendation-listp-of-cdr
  (implies (recommendation-listp recs)
           (recommendation-listp (cdr recs)))
  :hints (("Goal" :in-theory (enable recommendation-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun show-recommendation (rec)
  (declare (xargs :guard (recommendationp rec)))
  (let* ((name (nth 0 rec))
         (type (nth 1 rec))
         (object (nth 2 rec))
         (confidence-percent (nth 3 rec))
         ;; (book-map (car (nth 4 rec)))
         )
    (cw "~s0: Try ~x1 with ~x2 (conf: ~x3%).~%" name type object (floor confidence-percent 1))))

(defun show-recommendations-aux (recs)
  (declare (xargs :guard (recommendation-listp recs)
                  :guard-hints (("Goal" :in-theory (enable recommendation-listp)))))
  (if (endp recs)
      nil
    (prog2$ (show-recommendation (first recs))
            (show-recommendations-aux (rest recs)))))

;; Returns state because of the margin widening.
(defun show-recommendations (recs state)
  (declare (xargs :guard (recommendation-listp recs)
                  :stobjs state))
  (let ((state (acl2::widen-margins state)))
    (progn$ (show-recommendations-aux recs)
            (let ((state (acl2::unwiden-margins state)))
              state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund rec-confidence> (rec1 rec2)
  (declare (xargs :guard (and (recommendationp rec1)
                              (recommendationp rec2))))
  (> (nth 3 rec1) (nth 3 rec2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Everything must be the same except the name and confidence percent.
(defund equivalent-recommendationsp (rec1 rec2)
  (declare (xargs :guard (and (recommendationp rec1)
                              (recommendationp rec2))))
  (and (equal (nth 1 rec1) (nth 1 rec2))
       (equal (nth 2 rec1) (nth 2 rec2))
       (equal (nth 4 rec1) (nth 4 rec2))))
