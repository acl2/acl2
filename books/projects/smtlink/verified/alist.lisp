;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (March 8th 2020)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(include-book "std/util/top" :dir :system)

(defsection alists
  (encapsulate ;; generic properties of ACL2 alist's
    (((alist-key-p *) => *)
     ((alist-val-p *) => *)
     ((alist-val-as-bool *) => *))

    (local (define alist-key-p (x)
             :guard t
             :returns (ok booleanp)
             (and x (symbolp x))))
    (more-returns alist-key-p
                  (ok (booleanp ok) :name booleanp-of-alist-key-p))

    (local (define alist-val-p (x)
             :guard t
             :returns (ok booleanp)
             :enabled t
             (integerp x)))
    (more-returns alist-val-p
                  (ok (booleanp ok) :name booleanp-of-alist-val-p))

    (local (define alist-val-as-bool ((v alist-val-p))
             (declare (ignorable v))
             :returns (ok booleanp)
             t))
    (more-returns alist-val-as-bool
                  (ok (booleanp ok)
                      :name booleanp-of-alist-val-as-bool)))

  (define alist-consp (x)
    :guard t
    :returns (ok booleanp)
    (implies x (and (consp x) (alist-key-p (car x)) (alist-val-p (cdr x)))))

  (define maybe-alist-consp (x)
    :guard t
    :returns (ok booleanp)
    (implies x (alist-consp x)))

  (define maybe-alist-val-p (x)
    :guard t
    :returns (ok booleanp)
    (implies x (alist-val-p x)))

  (define alist-p (al)
    :guard t
    :returns (ok booleanp)
    (if (null al) t
      (and (consp al)
           (consp (car al))
           (alist-consp (car al))
           (alist-p (cdr al))))
    ///
    (more-returns
     (ok (implies ok (alistp al))
         :name alist-p-implies-alistp
         :hints(("Goal" :in-theory (enable alist-p))))))

  (defthm assoc-of-bogus-key
    (implies (and (alist-p al) (not (alist-key-p k)))
             (not (assoc-equal k al)))
    :hints(("Goal" :in-theory (enable alist-p alist-consp)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection arrays
  (define array-val-p (x)
    :guard t
    :returns (ok booleanp)
    (or (null x)
        (and (consp x)
             (alist-key-p (car x))
             (alist-val-p (cdr x)))))

  (define array-val-default ()
    :guard t
    :enabled t
    :returns (def array-val-p :hints(("Goal" :in-theory (enable array-val-p))))
    nil)

  (encapsulate ;; generic properties of arrays
    (((array-p *) => *)
     ((array-init) => *)
     ((array-store * * *) => *)
     ((array-select * *) => *))

    ;; We need to make our function definitions for array-p, array-init
    ;;   array-store, and array-select local, but the constraints (i.e.
    ;;   theorems) about them need to be exported from the encapsulation.
    ;;   I wrote the local definitions first, and then the exported
    ;;   more-returns theorems.
    (local (define array-p (ar)
             :guard t
             :returns (ok acl2::any-p)
             (if (null ar) t
               (and (consp ar)
                    (consp (car ar))
                    (alist-key-p (caar ar))
                    (array-val-p (cdar ar))
                    (array-p (cdr ar))))
             ///
             (more-returns
              (ok (implies ok (alistp ar))
                  :name array-p--implies--alistp
                  :hints(("Goal" :in-theory (enable array-p)))))))
    (more-returns array-p
                  (ok (booleanp ok) :name booleanp-of-array-p
                      :hints(("Goal" :in-theory (enable array-p)))))

    (local (define array-init ()
             :guard t
             :returns (ar acl2::any-p)
             nil))

    (local (define array-store ((ar0 array-p) (k alist-key-p) (v array-val-p))
             :returns (ar acl2::any-p)
             (if (and (alist-key-p k) (array-val-p v) (array-p ar0))
                 (acons k v ar0)
               nil)))

    (local (define array-select ((ar array-p) (k alist-key-p))
             :returns (v acl2::any-p)
             :guard-hints(("Goal"
                           :do-not-induct t
                           :in-theory (disable array-p--implies--alistp)
                           :use((:instance array-p--implies--alistp (ar ar)))))
             (if (and (alist-key-p k) (array-p ar) (assoc-equal k ar))
                 (cdr (assoc-equal k ar))
               (array-val-default))))

    ;; I'll be lazy and just enable all of local functions for arrays
    ;;   before proving their simple properties.
    (local (in-theory (enable array-p array-init array-store array-select)))

    (local (defthmd array-assoc-p-of-assoc-equal
             (implies (and (alist-key-p k) (array-p ar))
                      (or (null (assoc-equal k ar))
                          (and (alist-key-p (car (assoc-equal k ar)))
                               (array-val-p (cdr (assoc-equal k ar))))))
             :hints(("Goal" :in-theory (enable (array-p))))))

    (more-returns array-init
                  (ar (array-p ar) :name array-p-of-array-init))

    (more-returns array-store
                  (ar (array-p ar) :name array-p-of-array-store))

    (more-returns array-select
                  (v (array-val-p v)
                     :name array-val-p-of-array-select
                     :hints(
                            ("Goal"
                             :in-theory (enable array-p)
                             :use((:instance array-assoc-p-of-assoc-equal (k k) (ar ar))))
                            ("Subgoal 6"
                             :expand (hide (array-val-default)))))
                  (v (implies (not (alist-key-p k))
                              (equal v (array-val-default)))
                     :name array-select-of-bogus-key))

    (defthm array-select-of-array-init
      (equal (array-select (array-init) k) (array-val-default)))

    (defthm array-select-of-array-store
      (implies (and (alist-key-p k1) (alist-key-p k0) (array-val-p v0)
                    (array-p ar))
               (equal (array-select (array-store ar k0 v0) k1)
                      (if (equal k1 k0) v0 (array-select ar k1)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection equivalence-of-arrays-and-alists
  (defun-sk alist-array-equiv (al ar)
    (forall (k)
            (implies (and (array-p ar) (alist-p al) (alist-key-p k))
                     (equal (array-select ar k) (assoc-equal k al)))))

  (defthm alist-array-equiv--bogus-witness-implies-all-match
    (implies
     (and (alist-p al) (array-p ar) (alist-key-p k)
          (equal
           (array-select ar (alist-array-equiv-witness al ar))
           (assoc-equal  (alist-array-equiv-witness al ar) al)))
     (equal (array-select ar k) (assoc-equal k al)))
    :hints(("Goal"
            :in-theory (disable alist-array-equiv-necc)
            :use((:instance alist-array-equiv-necc (ar ar) (al al) (k k))))))

  (defthm equiv-of-array-alist-store
    (implies (and (array-p ar) (alist-p al)
                  (alist-key-p k) (alist-val-p v)
                  (alist-array-equiv al ar))
             (alist-array-equiv (acons k v al)
                                (array-store ar k (cons k v))))
    :hints(("Goal"
            :in-theory (e/d (array-val-p)
                            (alist-array-equiv-necc array-select-of-array-store))
            :use(
                 (:instance alist-array-equiv-necc (ar ar) (al al)
                            (k (alist-array-equiv-witness
                                (acons k v al)
                                (array-store ar k (cons k v)))))
                 (:instance array-select-of-array-store
                            (ar ar) (k0 k)
                            (k1 k) (v0 (cons k v)))
                 (:instance array-select-of-array-store
                            (ar ar) (k0 k) (v0 (cons k v))
                            (k1 (alist-array-equiv-witness (acons k v al)
                                                           (array-store ar k
                                                                        (cons k v))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection translation
  ;; Note: the proofs in this section are all straightforward -- they build
  ;;   on results from the previous two sections in "obvious" ways.  None of
  ;;   these proofs use induction.  When debugging these proofs I (mrg) often
  ;;   found it helpful to add a
  ;;     :do-non-induct t
  ;;   hint.  That way, when I missed enabling a function or instantiating a
  ;;   theorem, ACL2 fails with relatively easy easy to debug subgoals.  If
  ;;   ACL2 goes wild with induction, the proof debugging is harder (for me).
  (defthm translation-of-nil
    (alist-array-equiv nil (array-init)))

  (defthm translation-of-acons
    (implies
     (and (array-p ar) (alist-p al) (alist-key-p k)
          (alist-val-p v) (alist-array-equiv al ar))
     (alist-array-equiv (acons k v al)
                        (array-store ar k (cons k v))))
    :hints(("Goal"
            :in-theory (disable equiv-of-array-alist-store)
            :use((:instance equiv-of-array-alist-store (ar ar) (al al) (k k) (v v))))))

  (defthm translation-of-assoc-equal
    (implies (and (array-p ar) (alist-p al) (alist-key-p k)
                  (alist-array-equiv al ar))
             (equal (array-select ar k) (assoc-equal k al)))
    :hints(("Goal"
            :do-not-induct t
            :in-theory (disable alist-array-equiv--bogus-witness-implies-all-match)
            :use((:instance alist-array-equiv--bogus-witness-implies-all-match
                            (ar ar) (al al) (k k))))))
  )

;; TODO
(define alist-to-array ((al alist-p))
  :guard-hints(("Goal" :in-theory (enable alist-p)))
  :returns (ar array-p)
  (b* (((unless (mbt (alist-p al))) (array-init))
       ((unless (consp al)) (array-init))
       ((cons (cons key val) rest) al))
    (array-store (alist-to-array rest) key (cons key val)))
  ;; (if (and (consp (car al)) (alist-key-p (caar al)) (alist-val-p (cdar al)))
  ;;     (array-store (caar al) (cons (caar al) (cdar al)) (alist-to-array (cdr al)))
  ;;   (array-init))
  ///
  (local (in-theory (enable alist-to-array alist-p alist-consp)))
  (more-returns
   (ar (implies (and (alist-p al) (equal x ar))
                (alist-array-equiv al x))
       ;; :hints(("Goal" :in-theory (enable alist-p)))
       :name equiv-of-alist-to-array)))
