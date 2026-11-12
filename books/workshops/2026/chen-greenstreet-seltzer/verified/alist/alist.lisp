(in-package "SMT")
(include-book "std/util/top" :dir :system)
(include-book "array")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate ;; Type recognizers for indices and elements of alists
  (((ar-key-p *) => *)
   ((ar-val-p *) => *))

  (local (defun ar-key-p (x) (booleanp x)))
  (local (defun ar-val-p (x) (rationalp x)))

  (defthm booleanp-of-ar-key-p (booleanp (ar-key-p x)))
  (defthm booleanp-of-ar-val-p (booleanp (ar-val-p x))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; typed  alists

(define ar-key-val-consp (x)
  :returns (ok booleanp)
  :enabled t
  (and (consp x)
       (ar-key-p (car x))
       (ar-val-p (cdr x)))
  ///
  (more-returns
    (ok :name consp-when-ar-key-val-consp
	(implies ok (consp x)))))

(define ar-maybe-key-val-consp (x)
  :returns (ok booleanp)
  :enabled t
  (implies x (ar-key-val-consp x))
  ///
  (more-returns
    (ok :name ar-maybe-key-val-consp-when-ar-key-val-consp
	(implies (ar-key-val-consp x) ok))))

(define ar-key-val-alist-p (x)
  :returns (ok booleanp)
  (if x
      (and (consp x)
	   (ar-key-val-consp (car x))
	   (ar-key-val-alist-p (cdr x)))
      t)
  ///
  (more-returns
    (ok (implies ok (alistp x))
        :name alistp-when-ar-key-val-alist-p
	:hints(("Goal" :in-theory (enable ar-key-val-alist-p))))
    (ok (implies (and ok x) (consp x))
        :name consp-when-ar-key-val-alist-p)
    (ok (implies ok (ar-key-val-alist-p (cdr x)))
	:name cdr-when-ar-key-val-alist-p
	:hints(("Goal" :in-theory (enable ar-key-val-alist-p))))
    (ok (implies (and x ok)
                 (and (consp (car x)) (ar-key-val-consp (car x))))
	:name car-when-ar-key-val-alist-p
	:rule-classes (:rewrite (:forward-chaining :trigger-terms ((ar-key-val-alist-p x))))
	:hints(("Goal" :in-theory (enable ar-key-val-alist-p))))))

(in-theory (disable ar-key-val-consp ar-maybe-key-val-consp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ar-p and associated operators.
;; arrays that represents ar-key-val-alist-p values.

(acl2::define-sk ar-p (ar)
  (forall (k)
    (and (ua-p ar)
         (ar-maybe-key-val-consp (ua-select ar k))))
  ///
  (local (in-theory (enable ar-p)))
  (defthm ua-p-when-ar-p (implies (ar-p ar) (ua-p ar)))
  (defthm ar-p-of-ua-init (ar-p (ua-init nil))))

(define ar-init () ;; create an empty array
  :returns (ar)
  (ua-init nil)
  ///
  (in-theory (disable (:e ar-init)))
  (more-returns (ar (ar-p ar) :name ar-p-of-ar-init)))

(define ar-store ((ar ar-p) (k ar-key-p) (kv ar-maybe-key-val-consp))
  :returns (ar2 ar-p
    :hints(("Goal"
      :cases ((equal (ar-p-witness (ua-store ar k kv)) k))
      :in-theory (e/d (ar-p) (ar-p-necc))
      :use((:instance ar-p-necc (k (ar-p-witness (ua-store ar k kv))))))))
  (if (and (ar-key-p k) (ar-maybe-key-val-consp kv) (ar-p ar))
    (ua-store ar k kv)
    (ar-init)))

(define ar-select ((ar ar-p) (k ar-key-p))
  :returns (kv ar-maybe-key-val-consp)
  (if (ar-p ar)
    (ua-select ar k)
    nil))

(define ar-from-al ((al ar-key-val-alist-p)) ;; convert an alist to an array
  :returns (ar ar-p)
  :verify-guards nil
  (if (and (consp al) (ar-key-val-consp (car al)))
    (ar-store (ar-from-al (cdr al)) (caar al) (car al))
    (ar-init))
  ///
  (verify-guards ar-from-al ;; needs ar-p-of-ar-from-al
    :hints(("Goal" :in-theory (enable ar-key-val-consp)))))


(defthm ar-select-of-ar-init
  (equal (ar-select (ar-init) k) nil)
  :hints(("Goal" :in-theory (enable (:d ar-init) ar-select))))

(local (defthm ar-select-of-ar-store-when-keys-equal
  (implies (and (ar-p ar) (ar-key-p k) (ar-maybe-key-val-consp kv))
	   (equal (ar-select (ar-store ar k kv) k) kv))
  :hints(("Goal"
    :in-theory (e/d (ar-select ar-store) ())
    :use((:instance ar-p-of-ar-store))))))

(local (defthm ar-select-of-ar-store-when-keys-not-equal
  (implies (and (ar-p ar) (ar-key-p k0) (ar-maybe-key-val-consp kv0)
		(not (equal k1 k0)))
	   (equal (ar-select (ar-store ar k0 kv0) k1)
		  (ar-select ar k1)))
  :hints(("Goal"
    :in-theory (e/d (ar-select ar-store) (ar-p-of-ar-store))
    :use((:instance ar-p-of-ar-store (k k0) (kv kv0)))))))

(defthm ar-select-of-ar-store
  (implies (and (ar-p ar) (ar-key-p k0) (ar-maybe-key-val-consp kv0))
	   (equal (ar-select (ar-store ar k0 kv0) k1)
		  (if (equal k1 k0)
		      kv0
		      (ar-select ar k1)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; equivalence -- theorems that justify replacing operations on alists
;;   with operations on arrays.

(acl2::define-sk ar-equiv (al ar)
  :returns (ok booleanp)
  :verify-guards nil ;; we intend the stronger claim that ar-select and
  (forall (k)        ;; assoc-equal match even for "bad" keys.
    (and (ar-key-val-alist-p al)
	 (ar-p ar)
	 (equal (assoc-equal k al) (ar-select ar k)))))

(defthm ar-translation-of-nil
  (ar-equiv nil (ar-init))
  :hints(("Goal" :in-theory (enable ar-equiv))))

(defthm ar-translation-of-acons
  (implies (and (ar-equiv al ar)
		(ar-key-p k)
		(ar-val-p v))
	   (ar-equiv (cons (cons k v) al) (ar-store ar k (cons k v))))
  :hints(("Goal"
    :do-not-induct t
    :in-theory (e/d (ar-equiv ar-key-val-consp ar-key-val-alist-p)
		    (ar-equiv-necc))
    :use((:instance ar-equiv-necc
		    (k (ar-equiv-witness (cons (cons k v) al)
					 (ar-store ar k (cons k v)))))))))

(encapsulate ()
  (local (defthm lemma-base
           (implies (and (ar-key-val-alist-p al) (not (consp al)))
	            (ar-equiv al (ar-init)))
           :hints(("Goal" :cases (al)))))

  (local (defthm lemma-induct-lemma
           (implies (and (ar-key-val-alist-p al) (consp al))
	            (and (ar-key-p (caar al))
		         (ar-val-p (cdar al))))
           :hints(("Goal" :expand(
                                  (ar-key-val-alist-p al)
                                  (ar-key-val-consp (car al)))))))

  (local (defthm lemma-induct
           (let ((ar-cdr (ar-from-al (cdr al))))
             (implies (and (consp al)
		           (ar-equiv (cdr al) ar-cdr)
		           (ar-key-val-alist-p al))
	              (ar-equiv al (ar-store ar-cdr (caar al) (car al)))))
           :hints(("Goal"
                    :in-theory (e/d (ar-key-val-consp)
		                    (ar-translation-of-acons lemma-induct-lemma))
                    :use(
	                 (:instance ar-translation-of-acons
		                    (al (cdr al))
		                    (k  (caar al))
		                    (v  (cdar al))
		                    (ar (ar-from-al (cdr al))))
	                 (:instance lemma-induct-lemma (al al)))))))

  (defthm ar-translation-of-alist
    (implies (ar-key-val-alist-p al)
	     (ar-equiv al (ar-from-al al)))
    :hints(("Goal" :in-theory (enable ar-from-al))))

  (defthmd ar-translation-of-assoc-equal
    (implies (ar-equiv al ar)
	     (equal (assoc-equal k al) (ar-select ar k)))
    :hints(("Goal"
             :in-theory (e/d (ar-equiv ar-select) (ar-equiv-necc))
             :use((:instance ar-equiv-necc)))))

  (defthmd ar-top-down-translation-of-assoc-equal
    (implies (ar-key-val-alist-p al)
             (equal (assoc-equal k al)
                    (ar-select (ar-from-al al)
                               k)))
    :hints (("Goal"
              :in-theory (e/d (ar-equiv-necc)
                              (ar-translation-of-alist))
              :use ((:instance ar-translation-of-alist)))))

  (defthmd ar-top-down-translation-of-acons
    (implies (and (ar-key-p k)
                  (ar-val-p v))
             (equal (ar-from-al (cons (cons k v) al))
                    (ar-store (ar-from-al al) k (cons k v))))
    :hints (("Goal"
              :in-theory (enable ar-from-al
                                 ar-key-val-consp))))

  (defthmd ar-top-down-translation-of-nil
    (equal (ar-from-al nil)
           (ar-init))
    :hints (("Goal"
              :in-theory (enable ar-from-al)))))
