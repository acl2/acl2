;; define an alist that maps natural numbers to symbols, and then introduce
;; the theorems Smtlink needs to translate such alists to Z3 arrays.
;;
;; https://www.sandraboynton.com/sboynton/Amazing%20Cows%20interview.html

(in-package "SMT")
(include-book "std/util/top" :dir :system)
(include-book "alist")

(local (encapsulate nil
  (define kp (x)
    :returns (ok booleanp)
    (integerp x))

  (define vp (x)
    :returns (ok booleanp)
    (symbolp x))

  (define kvp (x)
    (and (consp x)
	 (kp (car x))
	 (vp (cdr x))))

  (define mkvp (x) (implies x (kvp x)))

  (define kvap (x)
    (if x
	(and (consp x)
	     (kvp (car x))
	     (kvap (cdr x)))
	t))

  (acl2::define-sk ar-kv-p (ar)
    :returns (ok)
    (forall (k)
      (and (ua-p ar)
	   (mkvp (ua-select ar k)))))

  (define ar-kv-init ()
    (ua-init nil)
    ///
    (in-theory (disable (:e ar-kv-init))))

  (define ar-kv-store ((ar ar-kv-p) (k kp) (kv mkvp))
    :verify-guards nil
    (if (and (kp k) (mkvp kv) (ar-kv-p ar))
	(ua-store ar k kv)
	(ar-kv-init)))

  (define ar-kv-from-al ((al kvap))
    :verify-guards nil
    (if (and (consp al) (kvp (car al)))
      (ar-kv-store (ar-kv-from-al (cdr al)) (caar al) (car al))
      (ar-kv-init)))

  (define ar-kv-select ((ar ar-kv-p) (k kp))
    (if (ar-kv-p ar)
	(ua-select ar k)
	nil))

  (acl2::define-sk ar-kv-equiv (al ar)
    :returns (ok)
    :verify-guards nil
    (forall (k)
	    (and (kvap al)
		 (ar-kv-p ar)
		 (equal (assoc-equal k al) (ar-kv-select ar k)))))

  ;; Rather than writing the long functional instantiation hint for each of the
  ;; theorems below, I'll wrap it up with a macro.
  (defmacro fi-thm (name claim ar-thm &optional theory)
    `(defthm ,name ,claim :hints(("Goal"
       :in-theory ,theory
       :use((:functional-instance ,ar-thm
				  ;; instantiate the generic functions
				  (ar-key-p kp)
				  (ar-val-p vp)
				  ;; instantiate the other relevant functions
				  (ar-key-val-consp kvp)
				  (ar-maybe-key-val-consp mkvp)
				  (ar-key-val-alist-p kvap)
				  (ar-p ar-kv-p)
				  (ar-p-witness ar-kv-p-witness)
				  (ar-init ar-kv-init)
				  (ar-store ar-kv-store)
				  (ar-from-al ar-kv-from-al)
				  (ar-select ar-kv-select)
				  (ar-equiv ar-kv-equiv)
				  (ar-equiv-witness ar-kv-equiv-witness)))))))


  ;; return type theorems
  ;;   In addition to providing returns theorems used by Smtlink, proving
  ;;   these theorems by functional instantiation has the salubrious effect
  ;;   of establishing the constraints for funcitional instantation one
  ;;   function at a time.  This seems to avoid having ACL2 generate a big,
  ;;   complicated constraint that it then is unable to discharge.

  (fi-thm booleanp-of-kvp
    (booleanp (kvp x))
    booleanp-of-ar-key-val-consp '(kvp booleanp-of-kp booleanp-of-vp))

  (fi-thm booleanp-of-mkvp
    (booleanp (mkvp x))
    booleanp-of-ar-maybe-key-val-consp '(mkvp (:t kvp)))

  (fi-thm booleanp-of-kvap
    (booleanp (kvap x))
    booleanp-of-ar-key-val-alist-p '(kvap))

  (encapsulate nil
    ;; booleanp-of-ar-kv-p can be prove using functional instantiation of
    ;;   booleanp-of-ar-p in the theory '(ar-kv-p ar-kv-p-necc).  So, why
    ;;   am I proving it by introducing three lemmas and using those?
    ;;   My reason is that the proof for boolean-p-of-ar-kv-equiv (below)
    ;;   fails with the corresponding hint.  I believe that's because the
    ;;   functional constraints require showing that the bodies of
    ;;   ar-kv-equiv and ar-kv-equiv-witness are what one would expect.
    ;;   Sadly, the rewrite rule for ar-kv-equiv-necc has a hypothesis of
    ;;     (ar-kv-equiv al ar)
    ;;   The corresponding term in the proof goal gets re-written by the
    ;;   rule (:d ar-kv-equiv), and then the rule for ar-kv-equiv-necc fails
    ;;   to match.  At least that's what I think is happening.
    ;;     I fixed the problem by using proof-builder to identify a sufficient
    ;;   set of lemmas, prove those, and then prove the main theorem.  I'm
    ;;   using the same approach here because I'm concerned that even though
    ;;   the more succinct proof just using theory '(ar-kv-p ar-kv-p-necc)
    ;;   succeeds, it may be sensitive to the order in which rewrites are
    ;;   performed.  The current proof seems likely to be more robust.
    ;;
    ;; Here's how I got the lemmas.  I gave the commands:
    ;;   ACL2 !> (verify (booleanp (ar-kv-equiv al ar)))
    ;;   ->: (use (:functional-instance booleanp-of-ar-equiv ...))
    ;;   ->: :s  ;; main.1 is trivial to discharge
    ;;   ->: :split  ;; produces 7 goals corresponding to the functional constraints.
    ;;   ->: print-all-goals
    ;; I stated a lemma for each of the goals printed above.  The lemma
    ;; main.4 is the contrapositive of main.1, and unused in the final proof;
    ;  so I don't state a lemma for it here.
    (local (defthm fi-ar-kv-p-1
      (implies (ar-kv-p ar) (ua-p ar))
      :hints(("Goal" :in-theory '(ar-kv-p-necc)))))

    (local (defthm fi-ar-kv-p-2
      (implies (ar-kv-p ar) (mkvp (ua-select ar k)))
      :hints(("Goal" :in-theory '(ar-kv-p-necc)))))

    (local (defthm fi-ar-kv-p-3
      (implies (ua-p ar)
	       (equal (ar-kv-p ar)
		      (mkvp (ua-select ar (ar-kv-p-witness ar)))))
      :hints(("Goal" :in-theory '(ar-kv-p)))))

   (fi-thm booleanp-of-ar-kv-p
     (booleanp (ar-kv-p ar))
     booleanp-of-ar-p '(fi-ar-kv-p-1 fi-ar-kv-p-2 fi-ar-kv-p-3)))

  (fi-thm ar-kv-p-of-ar-kv-init
    (ar-kv-p (ar-kv-init))
    ar-p-of-ar-init '(ar-kv-init))

  (fi-thm ar-kv-p-of-ar-kv-store
    (ar-kv-p (ar-kv-store ar k kv))
    ar-p-of-ar-store '(ar-kv-store))

  (verify-guards ar-kv-store)

  (fi-thm ar-kv-p-of-ar-kv-from-al
    (ar-kv-p (ar-kv-from-al al))
    ar-p-of-ar-from-al '(ar-kv-from-al))

  (verify-guards ar-kv-from-al
    :hints(("Goal"
      :in-theory '(ar-kv-p-of-ar-kv-from-al kvap mkvp kvp))))

  (fi-thm mkvp-of-ar-kv-select
    (mkvp (ar-kv-select ar k))
    ar-maybe-key-val-consp-of-ar-select '(ar-kv-select))

  ;; init select and store behave like they should for arrays
  (fi-thm ar-kv-select-of-ar-kv-init
    (equal (ar-kv-select (ar-kv-init) k) nil)
    ar-select-of-ar-init)

  (fi-thm ar-kv-select-of-ar-kv-store
    (implies (and (ar-kv-p ar) (kp k0) (mkvp kv0))
	     (equal (ar-kv-select (ar-kv-store ar k0 kv0) k1)
		    (if (equal k1 k0)
		      kv0
		      (ar-kv-select ar k1))))
    ar-select-of-ar-store)


  ;; translation of alist operations to operations on arrays
  (encapsulate nil
    ;; See the comments with the proof of booleanp-of-ar-kv-p to see
    ;;   how I came up with these lemmas and why.
    (local (defthm fi-ar-kv-equiv-1
      (implies (ar-kv-equiv al ar)
	       (kvap al))
      :hints(("Goal" :in-theory '(ar-kv-equiv-necc)))))

    (local (defthm fi-ar-kv-equiv-2
      (implies (ar-kv-equiv al ar)
	       (equal (assoc-equal k al) (ar-kv-select ar k)))
      :hints(("Goal" :in-theory '(ar-kv-equiv-necc)))))

    (local (defthm fi-ar-kv-equiv-3
      (implies (ar-kv-equiv al ar)
	       (ar-kv-p ar))
      :hints(("Goal" :in-theory '(ar-kv-equiv-necc)))))

    (local (defthm fi-ar-kv-equiv-5
      (implies (and (kvap al)
		    (ar-kv-p ar)
		    (equal (assoc-equal (ar-kv-equiv-witness al ar) al)
			   (ar-kv-select ar (ar-kv-equiv-witness al ar))))
	       (equal (ar-kv-equiv al ar) t))
      :hints(("Goal" :in-theory '(ar-kv-equiv)))))

    (fi-thm booleanp-of-ar-kv-equiv
      (booleanp (ar-kv-equiv al ar))
      booleanp-of-ar-equiv
      '(fi-ar-kv-equiv-1 fi-ar-kv-equiv-2 fi-ar-kv-equiv-3 fi-ar-kv-equiv-5)))

  (fi-thm ar-kv-translation-of-nil
    (ar-kv-equiv nil (ar-kv-init))
    ar-translation-of-nil)

  (fi-thm ar-kv-translation-of-acons
    (implies (and (ar-kv-equiv al ar)
		  (kp k)
		  (vp v))
	     (ar-kv-equiv (cons (cons k v) al) (ar-kv-store ar k (cons k v))))
    ar-translation-of-acons)

  (fi-thm ar-kv-translation-of-alist
    (implies (kvap al) (ar-kv-equiv al (ar-kv-from-al al)))
    ar-translation-of-alist)

  (fi-thm ar-kv-translation-of-assoc-equal
    (implies (ar-kv-equiv al ar)
	     (equal (assoc-equal k al) (ar-kv-select ar k)))
    ar-translation-of-assoc-equal)

  (fi-thm ar-kv-top-down-translation-of-assoc-equal
          (implies (kvap al)
                   (equal (assoc-equal k al)
                          (ar-kv-select (ar-kv-from-al al)
                                        k)))
          ar-top-down-translation-of-assoc-equal)

  (fi-thm ar-kv-top-down-translation-of-acons
          (implies (and (kp k)
                        (vp v))
                   (equal (ar-kv-from-al (cons (cons k v) al))
                          (ar-kv-store (ar-kv-from-al al) k (cons k v))))
          ar-top-down-translation-of-acons)

  (fi-thm ar-kv-top-down-translation-of-nil
          (equal (ar-kv-from-al nil)
                 (ar-kv-init))
          ar-top-down-translation-of-nil)
  ))


;; Having established the main results using kp and vp, I'll now restate
;; them with integerp and symbolp to produce the theorems needed by Smtlink.

(local (defthm integerp-equals-kp
  (equal (integerp x) (kp x))
  :hints(("Goal" :in-theory '(kp integerp)))))

(local (defthm symbolp-equals-vp
  (equal (symbolp x) (vp x))
  :hints(("Goal" :in-theory '(vp symbolp)))))

(define int-sym-consp (x)
  (and (consp x)
       (integerp (car x))
       (symbolp (cdr x))))

(local (defthm int-sym-consp-equals-kvp
  (equal (int-sym-consp x) (kvp x))
  :hints(("Goal"
    :in-theory '(integerp-equals-kp symbolp-equals-vp)
    :expand((int-sym-consp x) (kvp x))))))

(local (defthm booleanp-of-int-sym-consp
  (booleanp (int-sym-consp x))
  :hints(("Goal"
    :in-theory '(int-sym-consp-equals-kvp booleanp-of-kvp)))))

(define maybe-int-sym-consp (x)
  (implies x (int-sym-consp x)))

(local (defthm maybe-int-sym-consp-equals-mkvp
  (equal (maybe-int-sym-consp x) (mkvp x))
  :hints(("Goal"
    :in-theory '(maybe-int-sym-consp mkvp int-sym-consp-equals-kvp)))))

(local (defthm booleanp-of-maybe-int-sym-consp
  (booleanp (maybe-int-sym-consp x))
  :hints(("Goal"
    :in-theory '(maybe-int-sym-consp-equals-mkvp booleanp-of-mkvp)))))

(define int-sym-alist-p (x)
  (or (not x)
      (and (consp x)
	   (consp (car x))
	   (integerp (caar x))
	   (symbolp (cdar x))
	   (int-sym-alist-p (cdr x)))))

(local (defthm int-sym-alist-p-equals-kvap
  (equal (int-sym-alist-p x) (kvap x))
  :hints(("Goal"
    :in-theory (enable int-sym-alist-p kvap kvp)))))

(encapsulate
  (((int-sym-array-p *) => *)
   ((int-sym-array-init) => *)
   ((int-sym-array-store * * *) => *)
   ((int-sym-array-from-al *) => *)
   ((int-sym-array-select * *) => *)
   ((int-sym-array-equiv * *) => *))

  (local (defun int-sym-array-p (ar) (ar-kv-p ar)))
  (local (defun int-sym-array-init () (ar-kv-init)))
  (local (defun int-sym-array-store (ar k kv) (ar-kv-store ar k kv)))
  (local (defun int-sym-array-from-al (al) (ar-kv-from-al al)))
  (local (defun int-sym-array-select (ar k) (ar-kv-select ar k)))
  (local (defun int-sym-array-equiv (al ar) (ar-kv-equiv al ar)))

  ;; return type constraints
  (defthmd booleanp-of-int-sym-array-p
    (booleanp (int-sym-array-p ar))
    :hints(("Goal"
      :in-theory '(int-sym-array-p)
      :use((:instance booleanp-of-ar-kv-p (ar ar))))))

  (defthmd int-sym-array-p-of-int-sym-array-init
    (int-sym-array-p (int-sym-array-init))
    :hints(("Goal"
      :in-theory '(int-sym-array-init int-sym-array-p ar-kv-p-of-ar-kv-init))))

  (defthmd int-sym-array-p-of-int-sym-array-store
    (int-sym-array-p (int-sym-array-store ar k kv))
    :hints(("Goal"
      :in-theory '(int-sym-array-store int-sym-array-p ar-kv-p-of-ar-kv-store))))

  (defthmd int-sym-array-p-of-int-sym-array-from-al
    (int-sym-array-p (int-sym-array-from-al al))
    :hints(("Goal"
      :in-theory '(int-sym-array-from-al int-sym-array-p ar-kv-p-of-ar-kv-from-al))))

  (defthmd maybe-int-sym-cons-of-int-sym-array-select
    (maybe-int-sym-consp (int-sym-array-select ar k))
    :hints(("Goal"
      :in-theory '(int-sym-array-select maybe-int-sym-consp-equals-mkvp mkvp-of-ar-kv-select))))

  (defthmd booleanp-of-int-sym-array-equiv
    (booleanp (int-sym-array-equiv al ar))
    :hints(("Goal"
      :in-theory '(int-sym-array-equiv booleanp-of-ar-kv-equiv))))

  ;; array operation constraints
  (defthmd int-sym-array-select-of-int-sym-array-init
    (equal (int-sym-array-select (int-sym-array-init) k) nil)
    :hints(("Goal"
      :in-theory '(int-sym-array-select int-sym-array-init integerp-equals-kp)
      :use((:instance ar-kv-select-of-ar-kv-init)))))

  (defthmd int-sym-array-select-of-int-sym-array-store
    (implies (and (int-sym-array-p ar) (integerp k0) (maybe-int-sym-consp kv0))
	     (equal (int-sym-array-select (int-sym-array-store ar k0 kv0) k1)
		    (if (equal k1 k0)
			kv0
			(int-sym-array-select ar k1))))
    :hints(("Goal"
      :in-theory '(int-sym-array-select int-sym-array-store int-sym-array-p
		   integerp-equals-kp maybe-int-sym-consp-equals-mkvp)
      :use((:instance ar-kv-select-of-ar-kv-store)))))

  ;; translating alist values and operations to array versions
  (defthmd int-sym-translation-of-nil
    (int-sym-array-equiv nil (int-sym-array-init))
    :hints(("Goal"
      :in-theory '(int-sym-array-equiv int-sym-array-init
                   ar-kv-translation-of-nil))))

  (defthmd int-sym-translation-of-alist
    (implies (int-sym-alist-p al)
	     (int-sym-array-equiv al (int-sym-array-from-al al)))
    :hints(("Goal" :in-theory '(
      int-sym-alist-p-equals-kvap int-sym-array-equiv int-sym-array-from-al
      ar-kv-translation-of-alist))))

  (defthmd int-sym-translation-of-acons
    (implies (and (int-sym-array-equiv al ar)
		  (integerp k)
		  (symbolp v))
	     (int-sym-array-equiv (cons (cons k v) al)
				  (int-sym-array-store ar k (cons k v))))
    :hints(("Goal" :in-theory '(
      integerp-equals-kp symbolp-equals-vp int-sym-alist-p-equals-kvap
      int-sym-array-p int-sym-array-equiv int-sym-array-store
      ar-kv-translation-of-acons))))

  (defthmd int-sym-translation-of-assoc-equal
    (implies (int-sym-array-equiv al ar)
	     (equal (assoc-equal k al) (int-sym-array-select ar k)))
    :hints(("Goal" :in-theory '(
      int-sym-consp-equals-kvp int-sym-alist-p-equals-kvap integerp-equals-kp
      int-sym-array-p int-sym-array-equiv int-sym-array-select
                                ar-kv-translation-of-assoc-equal))))

  (defthmd int-sym-top-down-translation-of-assoc-equal
    (implies (int-sym-alist-p al)
             (equal (assoc-equal k al)
                    (int-sym-array-select (int-sym-array-from-al al)
                                          k)))
    :hints (("Goal"
              :in-theory '(integerp-equals-kp
                           symbolp-equals-vp
                           int-sym-alist-p-equals-kvap
                           int-sym-array-select
                           int-sym-array-from-al
                           ar-kv-top-down-translation-of-assoc-equal))))

  (defthmd int-sym-top-down-translation-of-acons
    (implies (and (integerp k)
                  (symbolp v))
             (equal (int-sym-array-from-al (cons (cons k v) al))
                    (int-sym-array-store (int-sym-array-from-al al)
                                         k
                                         (cons k v))))
    :hints (("Goal"
              :in-theory '(integerp-equals-kp
                           symbolp-equals-vp
                           int-sym-array-from-al
                           int-sym-array-store
                           ar-kv-top-down-translation-of-acons))))

  (defthmd int-sym-top-down-translation-of-nil
    (equal (int-sym-array-from-al nil)
           (int-sym-array-init))
    :hints (("Goal"
              :in-theory '(int-sym-array-from-al
                           int-sym-array-init
                           ar-kv-top-down-translation-of-nil)))))
