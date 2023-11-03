(in-package "ACL2")

(include-book "dargp-less-than")
(include-book "all-dargp")
(include-book "bounded-darg-listp")
(include-book "kestrel/typed-lists-light/all-less" :dir :system)

;; todo: there is already something called result-alistp

(local (in-theory (disable natp)))

;; Maps nodenum to the dargs to which they rewrote, or to nil if not yet handled.
(defund node-result-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist) ; disallow fast-alist name or size hint (for now)
    (let ((entry (first alist)))
      (and (consp entry) ;disallow non-conses
           (natp (car entry)) ; the nodenum
           (dargp (cdr entry)) ; the new darg
           (node-result-alistp (rest alist))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns the new darg for NODENUM, or nil if nodenum is not mapped to anything yet.
(defund lookup-node-in-node-result-alist (nodenum alist)
  (declare (xargs :guard (and (natp nodenum)
                              (node-result-alistp alist))))
  (cdr (hons-assoc-equal nodenum alist)))

(defthm dargp-of-lookup-node-in-node-result-alist
  (implies (and (node-result-alistp alist)
                (lookup-node-in-node-result-alist darg alist))
           (dargp (lookup-node-in-node-result-alist darg alist)))
  :hints (("Goal" :in-theory (e/d (lookup-node-in-node-result-alist node-result-alistp) (dargp)))))

;maybe disable?
(defthm natp-of-lookup-node-in-node-result-alist
  (implies (node-result-alistp alist)
           (equal (natp (lookup-node-in-node-result-alist nodenum alist))
                  (and (lookup-node-in-node-result-alist nodenum alist)
                       (not (consp (lookup-node-in-node-result-alist nodenum alist))))))
  :hints (("Goal" :in-theory (enable lookup-node-in-node-result-alist node-result-alistp hons-assoc-equal))))

;maybe disable?
(defthm true-listp-of-lookup-node-in-node-result-alist
  (implies (node-result-alistp alist)
           (equal (true-listp (lookup-node-in-node-result-alist nodenum alist))
                  (or (not (lookup-node-in-node-result-alist nodenum alist))
                      (consp (lookup-node-in-node-result-alist nodenum alist)))))
  :hints (("Goal" :in-theory (enable lookup-node-in-node-result-alist node-result-alistp hons-assoc-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Records the fact that NODENUM rewrite to DARG.
(defund update-node-result-alist (nodenum darg alist)
  (declare (xargs :guard (and (natp nodenum)
                              (node-result-alistp alist))))
  (hons-acons nodenum darg alist))

(defthm node-result-alistp-of-update-node-result-alist
  (implies (and (node-result-alistp alist)
                (natp nodenum)
                (dargp darg))
           (node-result-alistp (update-node-result-alist nodenum darg alist)))
  :hints (("Goal" :in-theory (enable update-node-result-alist node-result-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Keys that map to nil are not stored.  Once a key is bound it stays bound
(defund bounded-node-result-alistp (alist bound)
  (declare (xargs :guard (natp bound)))
  (if (atom alist)
      (null alist) ; disallow fast-alist name or size hint (for now)
    (let ((entry (first alist)))
      (and (consp entry) ;disallow non-conses
           (natp (car entry)) ; the nodenum
           (dargp-less-than (cdr entry) bound) ; the new darg
           (bounded-node-result-alistp (rest alist) bound)))))

(defthm bounded-node-result-alistp-of-nil
  (bounded-node-result-alistp nil bound)
  :hints (("Goal" :in-theory (enable bounded-node-result-alistp))))

(defthm bounded-node-result-alistp-forward-to-node-result-alistp
  (implies (bounded-node-result-alistp alist bound)
           (node-result-alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-node-result-alistp
                                     node-result-alistp))))

(defthm bounded-node-result-alistp-monotone-on-bound
  (implies (and (bounded-node-result-alistp alist free)
                (natp free)
                (<= free bound))
           (bounded-node-result-alistp alist bound))
  :hints (("Goal" :in-theory (enable bounded-node-result-alistp))))

;maybe disable?
(defthm dargp-less-than-of-lookup-node-in-node-result-alist
  (implies (bounded-node-result-alistp alist bound)
           (iff (dargp-less-than (lookup-node-in-node-result-alist nodenum alist) bound)
                (lookup-node-in-node-result-alist nodenum alist) ; node is bound to something
                ))
  :hints (("Goal" :in-theory (enable lookup-node-in-node-result-alist bounded-node-result-alistp hons-assoc-equal))))

;maybe disable?
(defthm <-of-lookup-node-in-node-result-alist
  (implies (and (bounded-node-result-alistp alist bound)
       ;         (natp nodenum)
                (lookup-node-in-node-result-alist nodenum alist) ; node is bound to something
                (not (consp (lookup-node-in-node-result-alist nodenum alist))))
           (< (lookup-node-in-node-result-alist nodenum alist) bound))
  :hints (("Goal" :in-theory (enable lookup-node-in-node-result-alist bounded-node-result-alistp hons-assoc-equal))))

(defthm bounded-node-result-alistp-of-update-node-result-alist
  (implies (and (bounded-node-result-alistp alist bound)
                (natp nodenum))
           (equal (bounded-node-result-alistp (update-node-result-alist nodenum darg alist) bound)
                  (dargp-less-than darg bound)))
  :hints (("Goal" :in-theory (enable update-node-result-alist node-result-alistp bounded-node-result-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Either returns nil (no args are unmapped) or extends acc with the unmapped args
;; See also get-args-not-done.
(defund get-unmapped-dargs (dargs alist acc unmapped-foundp)
  (declare (xargs :guard (and (all-dargp dargs)
                              (true-listp dargs) ; todo: it would be nice to have a darg-listp function
                              (node-result-alistp alist)
                              ;;(bounded-darg-listp dargs (alen1  alist))
                              (all-dargp acc)
                              (true-listp acc)
                              (booleanp unmapped-foundp))))
  (if (endp dargs)
      (if unmapped-foundp
          acc ; we extended acc
        nil ; return nil to indicate that all args were mapped to some result
        )
    (let* ((darg (first dargs)))
      (if (or (consp darg) ;it's a quotep, so skip it
              (lookup-node-in-node-result-alist darg alist) ;it's tagged as done, so skip it
              )
          (get-unmapped-dargs (rest dargs) alist acc unmapped-foundp)
        ;; add the arg and record the fact that we found an unmapped arg:
        (get-unmapped-dargs (rest dargs) alist (cons darg acc) t)))))

(defthm get-unmapped-dargs-when-acc-and-unmapped-foundp
  (implies (and acc unmapped-foundp)
           (get-unmapped-dargs dargs alist acc unmapped-foundp))
  :hints (("Goal" :in-theory (enable get-unmapped-dargs))))

(defthm all-<-of-get-unmapped-dargs
  (implies (and (all-< acc bound)
                (bounded-darg-listp dargs bound))
           (all-< (get-unmapped-dargs dargs alist acc unmapped-foundp) bound))
  :hints (("Goal" :in-theory (enable get-unmapped-dargs bounded-node-result-alistp))))

(defthm nat-listp-of-get-unmapped-dargs
  (implies (and (nat-listp acc)
                (all-dargp dargs))
           (nat-listp (get-unmapped-dargs dargs alist acc unmapped-foundp)))
  :hints (("Goal" :in-theory (enable get-unmapped-dargs bounded-node-result-alistp))))

(defthm lookup-node-in-alist-when-not-get-unmapped-dargs
  (implies (and (not (get-unmapped-dargs dargs alist acc untagged-foundp)) ;all args are done
                (member-equal darg dargs)
                (natp darg)
                (node-result-alistp alist))
           (lookup-node-in-node-result-alist darg alist))
  :hints (("Goal" :in-theory (enable get-unmapped-dargs
                                     lookup-node-in-node-result-alist
                                     member-equal
                                     node-result-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns the new darg for NODENUM, or nil if nodenum is not mapped to anything yet.
(defund lookup-darg-in-node-result-alist (darg alist)
  (declare (xargs :guard (and (dargp darg)
                              (node-result-alistp alist))))
  (if (consp darg) ; test for quotep
      darg
    ;; darg must be a nodenum:
    (lookup-node-in-node-result-alist darg alist)))

(defthm dargp-of-lookup-darg-in-node-result-alist
  (implies (and (node-result-alistp alist)
                (lookup-darg-in-node-result-alist darg alist)
                (dargp darg))
           (dargp (lookup-darg-in-node-result-alist darg alist)))
  :hints (("Goal" :in-theory (e/d (lookup-darg-in-node-result-alist) (dargp)))))

;; if we lookup a quotep, we get a quotep
(defthm consp-of-lookup-darg-in-node-result-alist
  (implies (and (consp darg) ; this case
                ; (node-result-alistp alist)
                ;(lookup-darg-in-node-result-alist darg alist)
                )
           (consp (lookup-darg-in-node-result-alist darg alist)))
  :hints (("Goal" :in-theory (e/d (lookup-darg-in-node-result-alist) (dargp)))))

(defthm not-consp-of-lookup-darg-in-node-result-alist-forward
  (implies (not (consp (lookup-darg-in-node-result-alist darg alist)))
           (not (consp darg)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (lookup-darg-in-node-result-alist) (dargp)))))

(defthm dargp-less-than-of-lookup-darg-in-node-result-alist
  (implies (and (bounded-node-result-alistp alist bound)
                (dargp darg))
           (iff (dargp-less-than (lookup-darg-in-node-result-alist darg alist) bound)
                (lookup-darg-in-node-result-alist darg alist)))
  :hints (("Goal" :in-theory (e/d (lookup-darg-in-node-result-alist) (dargp)))))

(defthm <-of-lookup-darg-in-node-result-alist
  (implies (and (not (consp (lookup-darg-in-node-result-alist darg alist)))
                (lookup-darg-in-node-result-alist darg alist)
                (bounded-node-result-alistp alist bound)
                (dargp darg))
           (< (lookup-darg-in-node-result-alist darg alist) bound))
  :hints (("Goal" :in-theory (e/d (lookup-darg-in-node-result-alist) (dargp)))))

(defthm lookup-darg-in-alist-when-not-get-unmapped-dargs
  (implies (and (not (get-unmapped-dargs dargs alist acc untagged-foundp)) ;all args are done
                (member-equal darg dargs)
                (dargp darg)
                (node-result-alistp alist))
           (lookup-darg-in-node-result-alist darg alist))
  :hints (("Goal" :in-theory (enable lookup-darg-in-node-result-alist))))

;maybe disable?
(defthm true-listp-of-lookup-darg-in-node-result-alist
  (implies (and (node-result-alistp alist)
                (dargp darg))
           (equal (true-listp (lookup-darg-in-node-result-alist darg alist))
                  (or (consp darg)
                      (not (lookup-darg-in-node-result-alist darg alist))
                      (consp (lookup-darg-in-node-result-alist darg alist)))))
  :hints (("Goal" :in-theory (enable lookup-darg-in-node-result-alist))))

(defthm natp-of-lookup-darg-in-node-result-alist
  (implies (and (node-result-alistp alist)
                ;;(dargp darg)
                )
           (equal (natp (lookup-darg-in-node-result-alist darg alist))
                  (and (not (consp darg))
                       (lookup-darg-in-node-result-alist darg alist)
                       (not (consp (lookup-darg-in-node-result-alist darg alist))))))
  :hints (("Goal" :in-theory (enable lookup-darg-in-node-result-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund lookup-dargs-in-node-result-alist (dargs alist)
  (declare (xargs :guard (and (true-listp dargs)
                              (all-dargp dargs)
                              (node-result-alistp alist))))
  (if (endp dargs)
      nil
    ;; TODO: Consider cons-with-hint here:
    (cons (lookup-darg-in-node-result-alist (first dargs) alist)
          (lookup-dargs-in-node-result-alist (cdr dargs) alist))))

(defthm len-of-lookup-dargs-in-node-result-alist
  (equal (len (lookup-dargs-in-node-result-alist dargs alist))
         (len dargs))
  :hints (("Goal" :in-theory (enable lookup-dargs-in-node-result-alist))))

(defthm all-dargp-of-lookup-dargs-in-node-result-alist-when-not-get-unmapped-dargs
  (implies (and (not (get-unmapped-dargs dargs alist acc unmapped-foundp))
                (all-dargp dargs)
                (node-result-alistp alist))
           (all-dargp (lookup-dargs-in-node-result-alist dargs alist)))
  :hints (("Goal" :in-theory (e/d (get-unmapped-dargs
                                   node-result-alistp
                                   lookup-dargs-in-node-result-alist
                                   lookup-darg-in-node-result-alist) (dargp)))))

(defthm bounded-darg-listp-of-lookup-dargs-in-node-result-alist-when-not-get-unmapped-dargs
  (implies (and (not (get-unmapped-dargs dargs alist acc unmapped-foundp))
                (all-dargp dargs)
                (bounded-node-result-alistp alist bound))
           (bounded-darg-listp (lookup-dargs-in-node-result-alist dargs alist) bound))
  :hints (("Goal" :in-theory (enable get-unmapped-dargs
                                     node-result-alistp
                                     all-dargp
                                     lookup-dargs-in-node-result-alist
                                     lookup-darg-in-node-result-alist
                                     dargp-less-than-of-lookup-node-in-node-result-alist))))

(defthmd not-get-unmapped-dargs-when-not-get-unmapped-dargs-and-subsetp-equal
  (implies (and (not (get-unmapped-dargs dargs2 alist acc unmapped-foundp))
                (subsetp-equal dargs dargs2))
           (not (get-unmapped-dargs dargs alist acc unmapped-foundp)))
  :hints (("Goal" :induct (subsetp-equal dargs dargs2)
           :in-theory (enable get-unmapped-dargs subsetp-equal))))

(defthm bounded-darg-listp-of-lookup-dargs-in-node-result-alist-when-not-get-unmapped-dargs-gen
  (implies (and (not (get-unmapped-dargs dargs2 alist acc unmapped-foundp))
                (subsetp-equal dargs dargs2)
                (all-dargp dargs)
                (bounded-node-result-alistp alist bound))
           (bounded-darg-listp (lookup-dargs-in-node-result-alist dargs alist) bound))
  :hints (("Goal" :use (:instance bounded-darg-listp-of-lookup-dargs-in-node-result-alist-when-not-get-unmapped-dargs)
           :in-theory (e/d (not-get-unmapped-dargs-when-not-get-unmapped-dargs-and-subsetp-equal)
                           (bounded-darg-listp-of-lookup-dargs-in-node-result-alist-when-not-get-unmapped-dargs)))))

(encapsulate ()
  (local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
  ;; cherrypick:
  ;; needed because the prover takes the cdr of the dargs in the myif case
  (defthm subsetp-equal-of-cdr-same
    (subsetp-equal (cdr x) x)))

;disable?
(defthm all-dargp-when-nat-listp-cheap
  (implies (nat-listp x)
           (all-dargp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-dargp nat-listp))))
