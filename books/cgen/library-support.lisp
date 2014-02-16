#|$ACL2s-Preamble$;
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis.lsp")
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

;record implementation
(include-book "defexec/other-apps/records/records" :dir :system)
;(include-book "finite-set-theory/osets/sets" :dir :system)
(include-book "std/osets/top" :dir :system)


;GETTING RECORDS TO behave nicely here are some
;;RECORDS THMS proven

#|
(thm (implies (and (not (ifmp v))
                   (consp v))
              (o< (acl2-count (mget x v))
                  (acl2-count v)))
     :hints (("goal" :induct (mget-wf x v))))
|#
(defthm records-lemma-acl2-count
  (implies (and (ifmp v)
                (acl2::well-formed-map v))
           (< (acl2-count (acl2::mget-wf x v))
              (acl2-count v)))
  :hints (("goal" :in-theory (enable acl2::mset acl2::mget acl2::mset-wf acl2::mget-wf acl2::acl2->map)))
  :rule-classes (:linear :rewrite))

(defthm records-acl2-count
  (implies (and (acl2::good-map v)
                (consp v))
           (< (acl2-count (acl2::mget x v))
               (acl2-count v)))
  :hints (("goal" :induct (acl2::mget-wf x v)
                  :in-theory (enable acl2::mset acl2::mget acl2::mset-wf acl2::mget-wf acl2::acl2->map)))
  :rule-classes (:linear :rewrite))

(defthm records-acl2-count-linear-arith-<=
  (<= (ACL2-COUNT (acl2::MGET k V))
      (ACL2-COUNT V))
  :hints (("goal" :in-theory (enable acl2::mset acl2::mget acl2::mset-wf acl2::mget-wf acl2::acl2->map)))
  :rule-classes (:linear :rewrite))

(defthm records-acl2-count-linear-arith-<
  (implies (and (not (equal k (acl2::ill-formed-key)))
                (acl2::MGET k V))
           (< (ACL2-COUNT (acl2::MGET k V))
              (ACL2-COUNT V)))
  :hints (("goal" :in-theory (enable acl2::mset acl2::mget acl2::mset-wf acl2::mget-wf acl2::acl2->map)))
  :rule-classes (:linear :rewrite))


 (defthm records-acl2-count2
  (implies (and (consp v)
                (not (equal x (ill-formed-key))))
           (< (acl2-count (mget x v))
              (acl2-count v)))
  :hints (("goal" :induct (mget-wf x v)
                  :in-theory (enable mset mget mset-wf mget-wf acl2->map)))
  :rule-classes ((:linear) (:rewrite)))

 (defthm field-not-empty-implies-record-not-empty1
   (implies (and (mget a x)
                 (not (equal a (ill-formed-key))))
            (consp x))
   :hints (("goal" :in-theory (enable mset mget mset-wf mget-wf acl2->map)))
   :rule-classes (:forward-chaining))
   ;               (:rewrite :backchain-limit-lst 1)))
 
(defthm field-not-empty-implies-record-not-empty2
  (implies (and (mget a x)
                ;(not (ifmp x))
                (good-map x))
           (consp x))
  :hints (("goal" :in-theory (enable mset mget mset-wf mget-wf acl2->map)))
  :rule-classes :forward-chaining) 

;The following theorem was needed in alloy-comparision
(defthm updating-empty-entry-with-nil-lemma
  (implies (equal (mget a r) v)
           (equal (mset a v r) r)))

(defthm updating-empty-entry-with-nil
  (implies (not (mget a r))
           (equal (mset a nil r) r)))

;This might be needed for termination arguments for SETS
(defthm non-nil-=>-not-empty
  (implies (and (set::setp v)
                (not (equal v nil)))
           (not (set::empty v)))
  :hints (("Goal" :in-theory (enable set::empty)))
  :rule-classes :forward-chaining)

;; (defthm good-map-implies-not-ifmp
;;   (implies (good-map x) 
;;            (and (not (ifmp x))
;;                 (well-formed-map x)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 1)
;;                  (:forward-chaining)))


(local
 (defthm mset-wf-key-non-nil-val-is-consp-lemma 
   (IMPLIES (AND V
                 (wf-keyp a)
                 (not (IFMP X)))
            (equal (IFMP (MSET-WF A V X)) nil))
   :hints (("goal" :in-theory (enable extensible-records)))))
               

(defthm mset-wf-key-non-nil-val-is-consp
 (IMPLIES (AND v
               (wf-keyp a))
          (consp (MSET A V x)))
 :hints (("goal" :in-theory (enable map->acl2 acl2->map extensible-records))))
