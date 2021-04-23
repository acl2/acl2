;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng and Mark Greenstreet (June 9th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/alists/alist-fix" :dir :system)
(include-book "std/lists/sets" :dir :system)
(include-book "centaur/fty/top" :dir :system)
;; To be compatible with Arithmetic books
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "clause-processors/unify-subst" :dir :system)

(include-book "../utils/pseudo-term")
(include-book "../utils/fresh-vars")
(include-book "evaluator")
(include-book "basics")
(include-book "cp-more")
(include-book "expand-options")

(set-state-ok t)

; There are *lots* of runes about pseudo-terms and many of them are :useless
;   (see :doc accumulated persistence).  The macro pseudo-useless disables
;   some of the typical offenders.
(defmacro pseudo-useless nil
  '(local (in-theory (disable pseudo-termp nil-of-assoc-equal-of-pseudo-term-alistp
                              acl2::pseudo-termp-opener pseudo-term-alistp-of-cons lambda-of-pseudo-lambdap
                              pseudo-lambdap-of-fn-call-of-pseudo-termp consp-of-pseudo-lambdap
                              pseudo-term-alistp-when-not-consp))))

; setting the induction-depth-limit isn't strictly needed, but it is a good
; check that we are following "the method" reasonably well.
(set-induction-depth-limit 1)

; Define types that we use: pseudo-callp, sym-int-alist, and
;   pseudo-term-sym-alist
(defsection types
  (pseudo-useless)

; pseudo-callp recognizes pseudo-terms that are function calls or lambdas
  (define pseudo-callp ((x acl2::any-p))
    :returns (ok booleanp)
    (and (pseudo-termp x) (consp x) (not (equal (car x) 'quote)))
    ///
; Here's a bunch of handy implications of knowing that a pseudo-term
; is a function call.  Should check to see if they are all needed.
    (more-returns
     (ok :name pseudo-callp-forward-chains-to-consp
	       (implies ok (consp x))
	       :rule-classes ((:forward-chaining))
	       :hints(("Goal" :expand ((pseudo-callp x)))))
     (ok :name pseudo-callp-forward-chains-to-pseudo-termp
	       (implies ok (pseudo-termp x))
	       :rule-classes ((:forward-chaining))
	       :hints(("Goal" :expand ((pseudo-callp x)))))
     (ok :name pseudo-callp-forward-chains-to-not-quote
	       (implies ok (not (equal (car x) 'quote)))
	       :rule-classes ((:forward-chaining))
	       :hints(("Goal" :expand ((pseudo-callp x)))))
     (ok :name pseudo-callp-forward-chains-to-pseudo-lambdap.1
	       (implies (and ok (consp (car x)))
		              (pseudo-lambdap (car x)))
	       :rule-classes ((:forward-chaining))
	       :hints(("Goal" :expand ((pseudo-callp x) (pseudo-termp x)))))
     (ok :name pseudo-callp-forward-chains-to-pseudo-lambdap.2
	       (implies (and ok (not (symbolp (car x))))
		              (pseudo-lambdap (car x)))
	       :rule-classes ((:forward-chaining))
	       :hints(("Goal" :expand ((pseudo-callp x) (pseudo-termp x)))))
     (ok :name pseudo-callp-forward-chains-to-symbolp.1
	       (implies (and ok (not (consp (car x))))
		              (symbolp (car x)))
	       :rule-classes ((:forward-chaining))
	       :hints(("Goal" :expand ((pseudo-callp x) (pseudo-termp x)))))
     (ok :name pseudo-callp-forward-chains-to-symbolp.2
	       (implies (and ok (not (pseudo-lambdap (car x))))
		              (symbolp (car x)))
	       :rule-classes ((:forward-chaining))
	       :hints(("Goal" :expand ((pseudo-callp x) (pseudo-termp x)))))
     (ok :name pseudo-callp-forward-chains-to-pseudo-term-listp
	       (implies ok (pseudo-term-listp (cdr x)))
	       :rule-classes ((:forward-chaining))
	       :hints(("Goal" :expand ((pseudo-callp x) (pseudo-termp x)))))
     (ok :name pseudo-callp-forward-chains-to-good-lambda-1
	       (implies (and ok (pseudo-lambdap (car x)))
	                (equal (len (car x)) 3))
	       :rule-classes ((:forward-chaining))
	       :hints(("Goal" :expand ((pseudo-callp x) (pseudo-termp x)))))
     (ok :name pseudo-callp-forward-chains-to-good-lambda-2
	       (implies (and ok (pseudo-lambdap (car x)))
	                (equal (len (cadar x)) (len (cdr x))))
	       :rule-classes ((:forward-chaining))
	       :hints(("Goal" :expand ((pseudo-callp x) (pseudo-termp x)))))
     (ok :name simple-vars-when-pseudo-callp
	       (implies ok
		              (acl2::set-equiv (acl2::simple-term-vars x)
				                           (acl2::simple-term-vars-lst (cdr x))))
	       :rule-classes ((:forward-chaining))
	       :hints(("Goal" :in-theory (enable acl2::simple-term-vars))))
     (ok :name pseudo-callp-when-pseudo-termp
         (implies (and (pseudo-termp x) (consp x) (not (equal (car x) 'quote)))
	                ok)
	       :rule-classes((:forward-chaining))
	       :hints(("Goal" :in-theory (enable pseudo-termp pseudo-callp))))
     (ok :name pseudo-callp-new-args
	       (implies (and ok (pseudo-term-listp new-args) (equal (len new-args) (len (cdr x))))
		              (pseudo-callp (cons (car x) new-args))))
     ))


  (defalist sym-int-alist
    :key-type symbolp
    :val-type integerp
    :true-listp t
    :pred sym-int-alistp)

  (defthm assoc-equal-of-sym-int-alist
    (implies (and (sym-int-alistp y)
		              (assoc-equal x y))
	           (and (consp (assoc-equal x y))
		              (integerp (cdr (assoc-equal x y))))))

; We use pseudo-term-sym-alists to map subterms of a goal to fresh variables
  (defalist pseudo-term-sym-alist
    :key-type pseudo-termp
    :val-type symbolp
    :true-listp t
    :pred pseudo-term-sym-alistp)

  (defthm assoc-equal-of-pseudo-term-sym-alist
    (implies (and (pseudo-term-sym-alistp y)
		              (assoc-equal x y))
	           (and (consp (assoc-equal x y))
		              (symbolp (cdr (assoc-equal x y))))))

  (define ptsa-avoid-p ((alst acl2::any-p) (avoid acl2::any-p))
    :returns (ok booleanp)
    (if (consp alst)
        (and (symbol-listp avoid)
	           (consp (car alst))
	           (pseudo-termp (caar alst))
	           (subsetp-equal (acl2::simple-term-vars (caar alst)) avoid)
	           (symbolp (cdar alst))
	           (cdar alst)
	           (member-equal (cdar alst) avoid)
	           (ptsa-avoid-p (cdr alst) avoid)
	           (not (member-equal (cdar alst)
			                          (acl2::simple-term-vars-lst (strip-cars alst))))
	           (not (member-equal (cdar alst)
			                          (strip-cdrs (cdr alst)))))
      (and (symbol-listp avoid)
	         (equal alst nil)))
    ///
    (local (defthm cdr-of-assoc
             (implies (assoc-equal x alst)
	                    (member-equal (cdr (assoc-equal x alst))
			                              (strip-cdrs alst)))
             :hints(("Goal" :in-theory (enable strip-cdrs)))))

    (local (defthm simple-term-vars-of-symbol
             (implies (symbolp x)
	                    (equal (acl2::simple-term-vars x)
		                         (if x (list x) nil)))
             :hints(("Goal" :expand (acl2::simple-term-vars x)))))

    (defthm symbol-list-of-union
      (implies (and (symbol-listp x) (symbol-listp y))
	             (symbol-listp (union-equal x y))))


    (more-returns
; Making all of these rules :rewrite and :forward-chaining is probably
; unnecessary.  We may speed-up rewriting by eliminating unneeded :rewrite
; rules.
     (ok :name ptsa-avoid-p-implies-pseudo-term-sym-alistp.alst
	       (implies ok (pseudo-term-sym-alistp alst))
	       :rule-classes((:rewrite) (:forward-chaining))
	       :hints(("Goal" :in-theory (enable ptsa-avoid-p))))
     (ok :name ptsa-avoid-p-implies-alistp.alst
	       (implies ok (alistp alst))
	       :rule-classes((:rewrite) (:forward-chaining))
	       :hints(("Goal" :in-theory (enable ptsa-avoid-p))))
     (ok :name ptsa-avoid-p-implies-symbol-listp.avoid
	       (implies ok (symbol-listp avoid))
	       :rule-classes((:rewrite) (:forward-chaining)))
     (ok :name ptsa-avoid-p-implies-true-listp.avoid
	       (implies ok (true-listp avoid))
	       :rule-classes((:rewrite) (:forward-chaining)))
     (ok :name ptsa-avoid-p-cdr
	       (implies ok (ptsa-avoid-p (cdr alst) avoid))
	       :hints(("Goal" :in-theory (enable ptsa-avoid-p))))
     (ok :name ptsa-avoid-p-subsetp
	       (implies (and ok (symbol-listp avoid2) (subsetp-equal avoid avoid2))
		              (ptsa-avoid-p alst avoid)))
     (ok :name ptas-avoid-p-union
	       (implies (and ok (symbol-listp more))
		              (ptsa-avoid-p alst (union-eq avoid more)))
	       :hints(("Goal" :in-theory (enable ptsa-avoid-p))))
     (ok :name ptsa-avoid-p-acons
	       (implies (and ok
		                   (pseudo-termp term)
		                   (symbolp s)
		                   s
		                   (subsetp-equal (acl2::simple-term-vars term) avoid)
		                   (not (member-equal s avoid)))
		              (ptsa-avoid-p (cons (cons term s) alst) (cons s avoid)))
	       :hints(("Goal" :in-theory (enable acl2::simple-term-vars-lst))))
     (ok :name assoc-when-ptsa-avoid-p
	       (implies ok
		              (subsetp-equal (acl2::simple-term-vars (cdr (assoc-equal x alst)))
				                         avoid))
	       :hints(("Goal" :in-theory (enable ptsa-avoid-p))))
     (ok :name cdr-assoc-when-ptsa-avoid-p
	       (implies (and ok (assoc-equal term alst))
		              (cdr (assoc-equal term alst)))
	       :hints(("Goal" :in-theory (enable ptsa-avoid-p))))))

  (define ptsa-avoid-fix ((alst pseudo-term-sym-alistp) (avoid symbol-listp))
    :returns (alst-fix pseudo-term-sym-alistp)
    :guard (ptsa-avoid-p alst avoid)
    (mbe :exec alst
	       :logic (if (ptsa-avoid-p alst avoid) alst nil))
    ///
    (more-returns
     (alst-fix :name ptsa-avoid-p-of-ptsa-fix
               (implies (symbol-listp avoid)
		                    (ptsa-avoid-p alst-fix avoid))
	             :hints(("Goal" :in-theory (enable ptsa-avoid-p))))
     (alst-fix :name ptsa-fix-when-ptsa-avoid-p
	             (implies (ptsa-avoid-p alst avoid) (equal alst-fix alst)))))


; generate-freshvar returns t if a term should be replaced by a fresh variable.
;   We require that generate-freshvar only returns t if term is a pseudo-callp.
;   One could further restrict the conditions under which a term can be replaced
;   by a variable without impacting the soundness of the clause processor.
  (define generate-freshvar ((term acl2::any-p))
    :returns (ok booleanp)
    (pseudo-callp term)
    ///
    (more-returns
     (ok :name generate-freshvar-forwards-to-pseudo-callp
	       (implies ok (pseudo-callp term))
	       :rule-classes ((:forward-chaining))
	       :hints(("Goal" :expand ((generate-freshvar term) (pseudo-callp term)))))))

; A few "obvious properties" of types defined elsewhere
  (defthm alistp-of-append-of-alistp
    (implies (and (alistp a1) (alistp a2))
	           (alistp (append a1 a2))))

  (defthm car-of-assoc
    (implies (assoc-equal x a)
	           (equal (car (assoc-equal x a)) x)))

  (defthm pseudo-term-list-fix-preserves-len
    (equal (len (pseudo-term-list-fix x)) (len x))
    :hints(("Goal" :in-theory (enable pseudo-term-list-fix))))

  (defthm len-when-pseudo-lambdap
    (implies (pseudo-lambdap x) (equal (len x) 3))
    :hints(("Goal" :expand (pseudo-lambdap x))))

  (defthm strip-cars-of-append
    (equal (strip-cars (append x y)) (append (strip-cars x) (strip-cars y))))

; There is only one hint using subsetp-growing in the code below.  It can
; probably be eliminated.
  (define subsetp-growing ((sets true-list-listp))
    :returns (growing booleanp)
    (or (endp (cdr sets))
	      (and (subsetp-equal (car sets) (cadr sets))
	           (subsetp-growing (cdr sets))))
    ///
    (more-returns
     (growing :name subsetp-growing-of-cdr
	            (implies growing (subsetp-growing (cdr sets)))
	            :hints(("Goal" :cases ((endp (cdr sets))))))
     (growing :name subsetp-growing-last
	            (implies growing
		                   (subsetp-equal (car sets) (car (last sets))))
	            :hints(("Goal" :in-theory (enable subsetp-growing)))))
    (in-theory (disable subsetp-growing-last)))


; There is only one use of with-b*-bindings in this book now.  I believe
; I can eliminate that and then delete ignor-vars and with-b*-bindings.
  (defun ignore-vars (x vars)
    (b* (((when (member x vars))
	        (intern-in-package-of-symbol (coerce (cons #\? (explode-atom x 10)) 'string) x))
	       ((unless (consp x)) x)
	       ((cons hd tl) x)
	       ((when (equal hd 'quote)) x))
      (cons (ignore-vars hd vars) (ignore-vars tl vars))))

  (defun with-b*-bindings (bindings term args)
    (list 'b*
          (ignore-vars bindings (cadr (member :ignore args)))
          term)))

(local (in-theory (enable subsetp-growing)))

(local ;; belongs in 'defsection types' but I don't know how to export it
 (defthm symbol-is-pseudo-term  ;; the defsection and keep it local to this book.
   (implies (symbolp x) (pseudo-termp x))))

(defsection pseudo-term-flag
  (pseudo-useless)
  (defines term-q
    :flag-local nil
    (define term-q ((term acl2::any-p))
      :returns (ok booleanp)
      (if (and (consp term)
	             (not (equal (car term) 'quote))
	             (true-listp term))
	        (list-q (cdr term))
	      t))

    (define list-q ((term-lst acl2::any-p))
      :returns (ok booleanp)
      (if (consp term-lst)
	        (and (term-q (car term-lst))
	             (list-q (cdr term-lst)))
	      (null term-lst))))

  ;; Need to show that pseudo-termp implies term-q and pseudo-term-listp
  ;; implies list-q.  This helps because defthm-term-q-flag theorems tend to
  ;; have hypotheses involving pseudo-termp and pseudo-term-listp, and showing
  ;; these implications allows those hypotheses to discharge goals generated
  ;; from term-q and list-q.
  (defthm-term-q-flag
    (defthm pseudo-termp--implies--term-q
      (implies (pseudo-termp term) (term-q term))
      :hints('(:expand ((term-q term))))
      :flag term-q)

    (defthm pseudo-term-listp--implies--list-q
      (implies (pseudo-term-listp term-lst) (list-q term-lst))
      :hints('(:expand ((list-q term-lst))))
      :flag list-q)))

(defsection alist-equiv-mod-keys
  (pseudo-useless)
  (define alist-equiv-mod-keys ((a1 alistp) (a2 alistp) (keys acl2::any-p))
    :returns (ok booleanp)
    (if (consp keys)
	      (and (equal (assoc-equal (car keys) a1)
		                (assoc-equal (car keys) a2))
	           (alist-equiv-mod-keys a1 a2 (cdr keys)))
      t)
    ///
    (local (in-theory (enable alist-equiv-mod-keys)))
    (more-returns
     (ok :name alist-equiv-mod-keys-member
	       (implies (and ok (member-equal k keys))
		              (equal (assoc-equal k a1) (assoc-equal k a2)))
	       :rule-classes((:rewrite :match-free :all))
	       :hints(("Goal" :in-theory (enable alist-equiv-mod-keys))))

     (ok :name alist-equiv-mod-keys-subsetp-eq
	       (implies (and ok (subsetp-eq keys2 keys))
		              (alist-equiv-mod-keys a1 a2 keys2))
	       :rule-classes ((:rewrite :match-free :all))
	       :hints(("Goal" :induct (alist-equiv-mod-keys a1 a2 keys2)))))

    (defthm alist-equiv-mod-keys-acons
      (implies (not (member-equal new-key keys))
	             (alist-equiv-mod-keys (cons (cons new-key new-val) a) a keys)))

    (defthm alist-equiv-mod-keys-car
      (implies (alist-equiv-mod-keys a1 a2 (acl2::simple-term-vars-lst term-lst))
	             (alist-equiv-mod-keys a1 a2 (acl2::simple-term-vars (car term-lst)))))

    (defthm alist-equiv-mod-keys-cdr
      (implies (alist-equiv-mod-keys a1 a2 (acl2::simple-term-vars-lst term-lst))
	             (alist-equiv-mod-keys a1 a2 (acl2::simple-term-vars-lst (cdr term-lst)))))

    (defthm alist-equiv-mod-keys--reflexive
      (alist-equiv-mod-keys a a keys))

    (defthm alist-equiv-mod-keys--commutative
      (implies (alist-equiv-mod-keys a1 a2 keys)
	             (alist-equiv-mod-keys a2 a1 keys))
      :rule-classes ((:rewrite :loop-stopper ((a1 a2)))))

    (defthm alist-equiv-mod-keys--transitive
      (implies (and (alist-equiv-mod-keys a1 a2 keys)
		                (alist-equiv-mod-keys a2 a3 keys))
	             (alist-equiv-mod-keys a1 a3 keys))
      :rule-classes((:forward-chaining :match-free :all))))

  (defthm alist-equiv-mod-keys-subsetp-equal
    (implies (and (subsetp-equal keys1 keys2)
		              (alist-equiv-mod-keys a1 a2 keys2))
	           (alist-equiv-mod-keys a1 a2 keys1))
    :hints(("Goal" :in-theory (enable alist-equiv-mod-keys))))

  (defthmd lemma-cong
    (implies (and (subsetp-equal keys1 keys2) 
		              (subsetp-equal keys2 keys1))
	           (equal (alist-equiv-mod-keys a1 a2 keys1)
	                  (alist-equiv-mod-keys a1 a2 keys2)))
    :hints(("Goal"
            :in-theory (disable alist-equiv-mod-keys-subsetp-equal)
            :use(
                 (:instance alist-equiv-mod-keys-subsetp-equal)
                 (:instance alist-equiv-mod-keys-subsetp-equal (keys1 keys2) (keys2 keys1))))))

  (defcong acl2::set-equiv equal (alist-equiv-mod-keys a1 a2 keys) 3
    :hints(("Goal"
            :expand ((acl2::set-equiv keys keys-equiv))
            :use((:instance lemma-cong (keys1 keys) (keys2 keys-equiv)))
            )))
  
  (in-theory (e/d (pseudo-termp) (symbol-listp))) ;; tweak the efficiency hint
  (defthm-term-q-flag
    (defthmd ev-smtcp-equivalent-environments
      (implies (and (pseudo-termp term)
		                (alistp a1)
		                (alistp a2)
		                (alist-equiv-mod-keys a1 a2 (acl2::simple-term-vars term)))
	             (equal (ev-smtcp term a1)
		                  (ev-smtcp term a2)))
      :flag term-q)
    (defthmd ev-smtcp-lst-equivalent-environments
      (implies (and (pseudo-term-listp term-lst)
		                (alistp a1)
		                (alistp a2)
		                (alist-equiv-mod-keys a1 a2 (acl2::simple-term-vars-lst term-lst)))
	             (equal (ev-smtcp-lst term-lst a1)
		                  (ev-smtcp-lst term-lst a2)))
      :flag list-q)
    :hints(("Goal" :in-theory (enable pseudo-callp ev-smtcp-of-fncall-args)))))

(defsection new-env
  (pseudo-useless)
  (define new-env ((alst pseudo-term-sym-alistp) (env alistp))
    :returns (env2 alistp)
    (if (endp alst)
	      (acl2::alist-fix env)
	    (acons (cdar alst)
	           (ev-smtcp (caar alst) (new-env (cdr alst) env))
	           (new-env (cdr alst) env)))
    ///
    (defthm new-env-of-nil
      (implies (alistp env)
	             (equal (new-env nil env) env))
      :hints(("Goal" :expand (new-env nil env))))
    (defthm new-env-of-append
      (equal
       (new-env (append alst1 alst2) env)
       (new-env alst1 (new-env alst2 env)))
      :hints(("Goal" :in-theory (enable new-env))))))

(defsection ev-smtcp-fresh-bindings
  (pseudo-useless)

; lemma-*1/3 is a "cut-and-paste" lemma from the proof for
;    alist-equiv-mod-keys--fresh-bindings whose induction step needs an
;    instance of alist-equiv-mod-keys-acons.
  (local (defthm lemma-*1/3
           (IMPLIES
	          (AND (ALIST-EQUIV-MOD-KEYS (NEW-ENV (CDR ALST) ENV)
				                               ENV AVOID)
	               (NOT (MEMBER-EQUAL (CDR (CAR ALST)) AVOID)))
	          (ALIST-EQUIV-MOD-KEYS (CONS (CONS (CDR (CAR ALST))
					                                    (EV-SMTCP (CAR (CAR ALST))
						                                            (NEW-ENV (CDR ALST) ENV)))
				                                (NEW-ENV (CDR ALST) ENV))
			                            ENV AVOID))
           :hints(("Goal"
                   :in-theory (disable alist-equiv-mod-keys-acons)
                   :use((:instance alist-equiv-mod-keys-acons
                                   (a (new-env (cdr alst) env)) (keys avoid) (new-key (cdr (car alst)))
	                                 (new-val (ev-smtcp (car (car alst)) (new-env (cdr alst) env)))))))))

  (local (defthm alist-equiv-mod-keys--fresh-bindings
           (implies (and (alistp env)
		                     (not (intersectp-equal (strip-cdrs alst) avoid)))
                    (alist-equiv-mod-keys (new-env alst env) env avoid))
           :hints(("Goal" :in-theory (enable new-env intersectp-equal)))))

  (defthm ev-smtcp-fresh-bindings
    (implies (and (pseudo-termp term)
		              (alistp env)
		              (symbol-listp avoid)
		              (subsetp-eq (acl2::simple-term-vars term) avoid)
		              (not (intersectp-equal (strip-cdrs alst) avoid)))
             (equal (ev-smtcp term (new-env alst env))
	                  (ev-smtcp term env)))
    :rule-classes ((:rewrite :match-free :all))
    :hints(("Goal"
            :in-theory (disable alist-equiv-mod-keys-subsetp-eq)
            :use(
	               (:instance ev-smtcp-equivalent-environments
	                          (a1 (new-env alst env))
	                          (a2 env))
	               (:instance alist-equiv-mod-keys-subsetp-eq
	                          (a1 (new-env alst env))
	                          (a2 env)
	                          (keys avoid)
	                          (keys2 (acl2::simple-term-vars term)))))))

  (defthm ev-smtcp-fresh-bindings-lst
    (implies (and (pseudo-term-listp term-lst)
		              (alistp env)
		              (symbol-listp avoid)
		              (subsetp-eq (acl2::simple-term-vars-lst term-lst) avoid)
		              (not (intersectp-equal (strip-cdrs alst) avoid)))
             (equal (ev-smtcp-lst term-lst (new-env alst env))
	                  (ev-smtcp-lst term-lst env)))
    :hints(("Goal"
            :in-theory (disable alist-equiv-mod-keys-subsetp-eq)
            :use(
	               (:instance ev-smtcp-lst-equivalent-environments
	                          (a1 (new-env alst env))
	                          (a2 env))
	               (:instance alist-equiv-mod-keys-subsetp-eq
	                          (a1 (new-env alst env))
	                          (a2 env)
	                          (keys avoid)
	                          (keys2 (acl2::simple-term-vars-lst term-lst))))))))


(defsection new-var-for-term
  (pseudo-useless)

; I moved the code for handling "bad" arguments to new-var-for-term to
; new-var-for-term-fix.  This avoids a cut-and-paste of the code into
; expand-term, I just call new-var-for-term-fix there as well.
  (define new-var-for-term-fix ((term pseudo-termp)
				                        (alst pseudo-term-sym-alistp)
				                        (avoid symbol-listp))
    :guard (and (subsetp-equal (acl2::simple-term-vars term) avoid)
		            (ptsa-avoid-p alst avoid))
    :returns (mv (ok booleanp)
		             (new-term pseudo-termp)
		             (new-alst pseudo-term-sym-alistp)
		             (new-avoid symbol-listp))
    (b* (((if (mbt (and (pseudo-termp term)
			                  (ptsa-avoid-p alst avoid)
			                  (subsetp-equal (acl2::simple-term-vars term) avoid))))
	        (mv t term alst avoid))
	       (term (pseudo-term-fix term))
	       (alst (if (ptsa-avoid-p alst avoid) alst nil))
	       (avoid (union-equal (symbol-list-fix avoid)
                             (acl2::simple-term-vars term))))
      (mv nil term alst avoid))
    ///
    (local (in-theory (enable new-var-for-term-fix)))
    (defthm new-var-for-term-fix-avoid-grows
      (subsetp-equal (symbol-list-fix avoid)
		                 (mv-nth 3 (new-var-for-term-fix term alst avoid))))

    (defthm new-var-for-term-fix-ensures-ptsa-avoid
      (ptsa-avoid-p (mv-nth 2 (new-var-for-term-fix term alst avoid))
		                (mv-nth 3 (new-var-for-term-fix term alst avoid)))
      :hints(("Goal" :expand ((:free (x) (ptsa-avoid-p nil x))))))

    (defthm new-var-for-term-fix-ok
      (equal (mv-nth 0 (new-var-for-term-fix term alst avoid))
	           (and (pseudo-termp term)
		              (ptsa-avoid-p alst avoid)
		              (subsetp-equal (acl2::simple-term-vars term) avoid)
		              (pseudo-term-sym-alistp alst)
		              (symbol-listp avoid)))
      :hints(("Goal" :in-theory (enable ptsa-avoid-p))))

    (defthm new-var-for-term-fix-not-ok
      (implies (not (mv-nth 0 (new-var-for-term-fix term alst avoid)))
	             (and (equal (mv-nth 1 (new-var-for-term-fix term alst avoid))
			                     (pseudo-term-fix term))
	                  (equal (mv-nth 2 (new-var-for-term-fix term alst avoid))
			                     (if (ptsa-avoid-p alst avoid) alst nil))
	                  (equal (mv-nth 3 (new-var-for-term-fix term alst avoid))
			                     (union-equal (symbol-list-fix avoid)
					                              (acl2::simple-term-vars (pseudo-term-fix term))))))))

  (define new-var-for-term ((term pseudo-termp)
			                      (alst pseudo-term-sym-alistp)
			                      (avoid symbol-listp))
    :guard (and (subsetp-equal (acl2::simple-term-vars term) avoid)
		            (ptsa-avoid-p alst avoid))
    :returns (mv (var pseudo-termp)
		             (new-alst pseudo-term-sym-alistp
		                       :hints(("Goal"
		                               :in-theory (disable ptsa-avoid-p-acons)
		                               :use((:instance ptsa-avoid-p-acons (s (new-fresh-var avoid))))))
		                       )
		             (new-avoid symbol-listp
			                      :hints(("Goal" :in-theory (enable ptsa-avoid-p)))))
    (b* (((mv ok-fix term-fix alst-fix avoid-fix) (new-var-for-term-fix term alst avoid))
	       ((unless ok-fix) (mv term-fix alst-fix avoid-fix))
	       ((unless (generate-freshvar term)) (mv term alst avoid))
	       (new-var (new-fresh-var avoid)))
      (mv new-var (acons term new-var alst) (cons new-var avoid)))
    ///
    (local (in-theory (enable new-var-for-term)))


; Any new variable introduced by new-var-for-term was not already
; an element of avoid.
    (defthm new-var-for-term-avoid
      (implies (symbol-listp avoid)
	             (let ((var (mv-nth 0 (new-var-for-term term alst avoid))))
		             (or (equal var (pseudo-term-fix term))
			               (and (symbolp var)
			                    (not (member-equal var avoid)))))))

    ;; new-avoid contains avoid
    (defthm new-var-for-term-avoid-grows
      (implies (symbol-listp avoid)
	             (subsetp-eq avoid (mv-nth 2 (new-var-for-term term alst avoid)))))

    
    (defthm new-var-for-term-ptsa-avoid
      (ptsa-avoid-p (mv-nth 1 (new-var-for-term term alst avoid))
		                (mv-nth 2 (new-var-for-term term alst avoid)))
      :hints(("Goal"
	            :expand ((:free (avoid) (ptsa-avoid-p nil avoid)))
	            :in-theory (disable ptsa-avoid-p-acons)
	            :use((:instance ptsa-avoid-p-acons (s (new-fresh-var avoid)))))))

    (defthm new-var-for-term-new-avoid
      (subsetp-eq
       (acl2::simple-term-vars (mv-nth 0 (new-var-for-term term alst avoid)))
       (mv-nth 2 (new-var-for-term term alst avoid)))
      :hints(("Goal"
              :expand ((acl2::simple-term-vars (new-fresh-var avoid))))))

    ;; Evaluating var with new-alst produces the same value as evaluating
    ;; term with alst.
    (defthm new-var-for-term--var-equal-term
      (implies (and (pseudo-termp term)
		                (ptsa-avoid-p alst avoid)
		                (alistp env))
	             (mv-let (var new-alst new-avoid)
		             (new-var-for-term term alst avoid)
		             (declare (ignore new-avoid))
		             (equal (ev-smtcp var (new-env new-alst env))
			                  (ev-smtcp term (new-env alst env)))))
	    :hints(("Goal"
	            :expand((new-env (cons (cons term (new-fresh-var avoid)) alst) env))
	            :in-theory (enable ptsa-avoid-p))))

    ;; Evaluating any term (e.g. x) whose free variables are all in avoid
    ;; produces the same value with alst and new-alst
    (defthm new-var-for-term-preserves-ev-smtcp
      (implies (and (pseudo-termp term)
		                (ptsa-avoid-p alst avoid)
		                (pseudo-termp x)
		                (subsetp-equal (acl2::simple-term-vars x) avoid)
		                (alistp env))
	             (let ((new-alst (mv-nth 1 (new-var-for-term term alst avoid))))
		             (equal (ev-smtcp x (new-env new-alst env))
			                  (ev-smtcp x (new-env alst env)))))
	    :hints(("Goal"
	            :in-theory (e/d (ptsa-avoid-p new-env intersectp-equal)
		                          (ev-smtcp-fresh-bindings))
	            :use((:instance ev-smtcp-fresh-bindings
	                            (term x)
	                            (env (new-env alst env))
	                            (alst (cons (cons term (new-fresh-var avoid)) nil)))))))

    ;; Evaluating any term-list (e.g. xlst) whose free variables are all in
    ;; avoid produces the same value with alst and new-alst
    (defthm new-var-for-term-preserves-ev-smtcp-lst
      (implies (and (pseudo-termp term)
		                (ptsa-avoid-p alst avoid)
		                (pseudo-term-listp xlst)
		                (subsetp-equal (acl2::simple-term-vars-lst xlst) avoid)
		                (alistp env))
	             (let ((new-alst (mv-nth 1 (new-var-for-term term alst avoid))))
		             (equal (ev-smtcp-lst xlst (new-env new-alst env))
			                  (ev-smtcp-lst xlst (new-env alst env)))))
      :hints(("Goal"
	            :in-theory (e/d (ptsa-avoid-p) (new-var-for-term))
	            :induct (true-listp xlst))))))

(defsection new-vars-for-term-list
  (pseudo-useless)

  (define new-vars-for-term-list-fix ((term-lst pseudo-term-listp)
				                              (alst pseudo-term-sym-alistp)
				                              (avoid symbol-listp))
    :guard (and (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid)
		            (ptsa-avoid-p alst avoid))
    :returns (mv (ok booleanp)
		             (new-term-lst pseudo-term-listp)
		             (new-alst pseudo-term-sym-alistp)
		             (new-avoid symbol-listp))
    (b* (((if (mbt (and (pseudo-term-listp term-lst)
			                  (ptsa-avoid-p alst avoid)
			                  (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid))))
	        (mv t term-lst alst avoid))
	       (term-lst (pseudo-term-list-fix term-lst))
	       (alst (if (ptsa-avoid-p alst avoid) alst nil))
	       (avoid (union-equal (symbol-list-fix avoid)
                             (acl2::simple-term-vars-lst term-lst))))
      (mv nil term-lst alst avoid))
    ///
    (local (in-theory (enable new-vars-for-term-list-fix)))
    (defthm new-vars-for-term-list-fix-avoid-grows
      (subsetp-equal (symbol-list-fix avoid)
		                 (mv-nth 3 (new-vars-for-term-list-fix term-lst alst avoid))))

    (defthm new-vars-for-term-list-fix-ensures-ptsa-avoid
      (ptsa-avoid-p (mv-nth 2 (new-vars-for-term-list-fix term-lst alst avoid))
		                (mv-nth 3 (new-vars-for-term-list-fix term-lst alst avoid)))
      :hints(("Goal" :expand ((:free (x) (ptsa-avoid-p nil x))))))

    (defthm new-vars-for-term-list-fix-ok
      (equal (mv-nth 0 (new-vars-for-term-list-fix term-lst alst avoid))
	           (and (pseudo-term-listp term-lst)
		              (ptsa-avoid-p alst avoid)
		              (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid)
		              (pseudo-term-sym-alistp alst)
		              (symbol-listp avoid)))
      :hints(("Goal" :in-theory (enable ptsa-avoid-p))))

    (defthm new-vars-for-term-list-fix-not-ok
      (implies (not (mv-nth 0 (new-vars-for-term-list-fix term-lst alst avoid)))
	             (and (equal (mv-nth 1 (new-vars-for-term-list-fix term-lst alst avoid))
			                     (pseudo-term-list-fix term-lst))
	                  (equal (mv-nth 2 (new-vars-for-term-list-fix term-lst alst avoid))
			                     (if (ptsa-avoid-p alst avoid) alst nil))
	                  (equal (mv-nth 3 (new-vars-for-term-list-fix term-lst alst avoid))
			                     (union-equal (symbol-list-fix avoid)
					                              (acl2::simple-term-vars-lst (pseudo-term-list-fix term-lst))))))))

  (define new-vars-for-term-list ((term-lst pseudo-term-listp)
				                          (alst pseudo-term-sym-alistp)
				                          (avoid symbol-listp))
    :measure (len term-lst)
    :hints(("Goal" :expand ((pseudo-term-list-fix term-lst))))
    :guard (and (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid)
		            (ptsa-avoid-p alst avoid))
    :returns (mv (vars pseudo-term-listp)
		             (new-alst pseudo-term-sym-alistp)
		             (new-avoid symbol-listp))
    :verify-guards nil
    (b* (((mv ok-fix term-lst-fix alst-fix avoid-fix)
	        (new-vars-for-term-list-fix term-lst alst avoid))
	       ((unless ok-fix) (mv term-lst-fix alst-fix avoid-fix))
	       ((unless (consp term-lst)) (mv term-lst alst avoid))
	       ((cons lst-hd lst-tl) term-lst)
	       ((mv var-hd alst-1 avoid-1)
	        (new-var-for-term lst-hd alst avoid))
	       ((mv vars-tl alst-2 avoid-2)
	        (new-vars-for-term-list lst-tl alst-1 avoid-1)))
      (mv (cons var-hd vars-tl) alst-2 avoid-2))
    ///
    (more-returns
     (vars :name new-vars-for-term-list-preserves-len
	         (equal (len vars) (len term-lst))
	         :hints(("Goal" :expand ((pseudo-term-list-fix term-lst))))))

    ;; The properties that we prove for new-vars-for-term-list are analagous
    ;;   to those proven above for new-vars-for-term
    (local (in-theory (enable new-vars-for-term-list)))

    (local (defmacro with-my-bindings (term &rest args)
             (with-b*-bindings
	            '((term-lst (pseudo-term-list-fix term-lst))
	              (alst (pseudo-term-sym-alist-fix alst))
	              (avoid (symbol-list-fix avoid))
	              ((cons lst-hd lst-tl) term-lst)
	              ((mv var-hd alst-1 avoid-1)
	               (new-var-for-term lst-hd alst avoid)))
              term args)))

    (defthm new-vars-for-term-list-avoid-grows
      (implies (symbol-listp avoid)
	             (subsetp-eq avoid (mv-nth 2 (new-vars-for-term-list term-lst alst avoid)))))

    (defthm new-vars-for-term-list-ptsa-avoid
      (ptsa-avoid-p (mv-nth 1 (new-vars-for-term-list term-lst alst avoid))
	                  (mv-nth 2 (new-vars-for-term-list term-lst alst avoid)))
      :hints(("Goal" :in-theory (enable ptsa-avoid-p))))

    (local (defthm avoid-3-lemma
             (b* (((cons hd tl)term-lst)
	                ((mv hd-var alst-1 avoid-1)
	                 (new-var-for-term hd alst avoid))
	                (avoid-2 (mv-nth 2 (new-vars-for-term-list tl alst-1 avoid-1))))
	             (implies (and (symbol-listp avoid)
		                         (subsetp-equal (acl2::simple-term-vars hd) avoid))
	                      (subsetp-equal (acl2::simple-term-vars hd-var) avoid-2)))
             :hints(("Goal"
	                   :in-theory (disable new-var-for-term-new-avoid)
	                   :use(
	                        (:instance new-var-for-term-new-avoid (term (car term-lst))))))))

    (defthm new-vars-for-term-list-new-avoid-3
      (implies (and (symbol-listp avoid)
		                (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid))
	             (mv-let (vars new-alst new-avoid)
		             (new-vars-for-term-list term-lst alst avoid)
		             (declare (ignore new-alst))
		             (subsetp-eq (acl2::simple-term-vars-lst vars) new-avoid)))
      :hints(("Goal"
	            :in-theory (enable acl2::simple-term-vars-lst))))

    (verify-guards new-vars-for-term-list
      :hints(
             ("Goal"
	            :use (
	                  (:instance subsetp-growing-last (sets
	                                                   (with-my-bindings
	                                                    (list (ACL2::SIMPLE-TERM-VARS-LST (CDR TERM-LST))
		                                                        (ACL2::SIMPLE-TERM-VARS-LST TERM-LST)
		                                                        AVOID AVOID-1)
	                                                    :ignore (lst-tl var-hd alst-1))))))))
	  
    ;; The evaluation of any term (e.g. x) whose free variables are all in
    ;; avoid produces the same result with alst and new-alst
    (defthm new-vars-for-term-list-preserves-ev-smtcp
      (implies (and (pseudo-term-listp term-lst)
		                (ptsa-avoid-p alst avoid)
		                (pseudo-termp x)
		                (subsetp-equal (acl2::simple-term-vars x) avoid)
		                (alistp env))
	             (mv-let (vars new-alst new-avoid)
		             (new-vars-for-term-list term-lst alst avoid)
		             (declare (ignore vars new-avoid))
		             (equal (ev-smtcp x (new-env new-alst env))
			                  (ev-smtcp x (new-env alst env)))))
	    :hints(("Goal"
	            :induct (new-vars-for-term-list term-lst alst avoid)
	            :in-theory (enable new-env intersectp-equal))))

    ;; The evaluation of any term-list (e.g. xlst) whose free variables are
    ;; all in avoid produces the same result with alst and new-alst
    (defthm new-vars-for-term-list-preserves-ev-smtcp-lst
      (implies (and (pseudo-term-listp term-lst)
		                (ptsa-avoid-p alst avoid)
		                (pseudo-term-listp xlst)
		                (subsetp-equal (acl2::simple-term-vars-lst xlst) avoid)
		                (alistp env))
	             (mv-let (vars new-alst new-avoid)
		             (new-vars-for-term-list term-lst alst avoid)
		             (declare (ignore vars new-avoid))
		             (equal (ev-smtcp-lst xlst (new-env new-alst env))
			                  (ev-smtcp-lst xlst (new-env alst env))))))

    (defthm ev-smtcp-lst-equal-vars-term-lst
      (implies (and (pseudo-term-listp term-lst)
		                (ptsa-avoid-p alst avoid)
		                (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid)
		                (alistp env))
	             (mv-let (vars new-alst new-avoid)
		             (new-vars-for-term-list term-lst alst avoid)
		             (declare (ignore new-avoid))
		             (equal (ev-smtcp-lst vars (new-env new-alst env))
			                  (ev-smtcp-lst term-lst (new-env alst env)))))
	    :hints(("Goal" :in-theory (enable acl2::simple-term-vars-lst))))))

(defsection function-substitution
  (pseudo-useless)
  (define function-substitution ((x pseudo-termp) state)
    :returns (mv (successp booleanp) (x1 pseudo-termp))
    :guard-hints(("Goal" :in-theory (enable pseudo-termp)))
    (b* (((unless (pseudo-callp x)) (mv nil (pseudo-term-fix x)))
         (fn (acl2::ffn-symb x))
         ((when (acl2::flambdap fn))
          (b* ((formals (lambda-formals fn))
               (body (lambda-body fn))
               (args (acl2::fargs x)))
            (mv t (acl2::substitute-into-term body (pairlis$ formals args)))))
         (formula (acl2::meta-extract-formula-w fn (w state)))
         ((unless (pseudo-termp formula)) (mv nil x))
         ((mv ok lhs rhs)
          (case-match formula
            (('equal lhs rhs)
             (mv t lhs rhs))
            (& (mv nil nil nil))))
         ((unless ok) (mv nil x))
         ((mv match-ok subst) (acl2::simple-one-way-unify lhs x nil))
         ((unless match-ok) (mv nil x)))
      (mv t (acl2::substitute-into-term rhs subst))))


  (defthm correctness-of-function-substitution
    (implies (and (ev-smtcp-meta-extract-global-facts)
		              (pseudo-termp term))
	           (equal (ev-smtcp (mv-nth 1 (function-substitution term state)) a)
		                (ev-smtcp term a)))
    :hints (("Goal"
	           :in-theory (e/d (function-substitution)
			                       (w ev-smtcp-meta-extract-formula))
	           :use ((:instance ev-smtcp-meta-extract-formula
				                      (name (car term))
				                      (st state)
				                      (a (ev-smtcp-alist
				                          (mv-nth 1
					                                (acl2::simple-one-way-unify
					                                 (cadr (meta-extract-formula (car term) state))
					                                 term nil))
				                          a)))))))

  (local (defthmd simple-term-vars-of-function-substitution-lemma
           (implies (pseudo-callp term)
	                  (subsetp-equal (acl2::simple-term-vars (mv-nth 1 (function-substitution term state)))
			                             (acl2::simple-term-vars-lst (cdr term))))
           :hints(("Goal"
	                 :in-theory (e/d
	                             (function-substitution acl2::simple-term-vars acl2::simple-term-vars-lst)
	                             (acl2::simple-term-vars-of-simple-one-way-unify
	                              acl2::simple-term-vars-of-substitute-into-term))
	                 :use(
	                      (:instance acl2::simple-term-vars-of-simple-one-way-unify
	                                 (pat (cadr (acl2::meta-extract-formula-w (car term) (w state))))
	                                 (term term)
	                                 (alst nil)
	                                 (all-vars (acl2::simple-term-vars-lst (cdr term))))
	                      (:instance acl2::simple-term-vars-of-substitute-into-term
	                                 (x (caddr (car term)))
	                                 (al (pairlis$ (cadr (car term)) (cdr term))))
	                      (:instance acl2::simple-term-vars-of-substitute-into-term
	                                 (x (caddr (acl2::meta-extract-formula-w (car term) (w state))))
	                                 (al (mv-nth 1 (acl2::simple-one-way-unify
	                                                (cadr (acl2::meta-extract-formula-w (car term) (w state)))
			                                            term nil)))))))))

  (defthm simple-term-vars-of-function-substitution
    (implies (pseudo-termp term)
	           (subsetp-equal (acl2::simple-term-vars (mv-nth 1 (function-substitution term state)))
			                      (acl2::simple-term-vars term)))
    :hints(("Goal"
	          :in-theory (disable simple-term-vars-of-function-substitution-lemma)
            :use((:instance function-substitution (x term))
	               (:instance simple-term-vars-of-function-substitution-lemma)))))

  (defthm function-substitution-with-new-args
    (implies (and (pseudo-callp x)
		              (pseudo-term-listp new-args)
		              (ptsa-avoid-p alst avoid)
		              (subsetp-equal (acl2::simple-term-vars-lst new-args) avoid)
		              (equal (len new-args) (len (cdr x))))
	           (subsetp-equal
	            (acl2::simple-term-vars
	             (mv-nth 1
	                     (function-substitution 
		                    (cons (car x) (mv-nth 0 (new-vars-for-term-list new-args alst avoid)))
		                    state)))
	            (mv-nth 2 (new-vars-for-term-list new-args alst avoid))))
    :hints(("Goal"
	          :in-theory (e/d (acl2::simple-term-vars)
			                      (simple-term-vars-of-function-substitution
			                       new-vars-for-term-list-new-avoid-3))
	          :use(
	               (:instance simple-term-vars-of-function-substitution
	                          (term (cons (car x) (mv-nth 0 (new-vars-for-term-list new-args alst avoid)))))
	               (:instance new-vars-for-term-list-new-avoid-3
	                          (term-lst new-args)))))))


(defsection fn-lvls
  (local (pseudo-useless))

  (define update-fn-lvls ((fn acl2::any-p)
			                    (options expand-options-p)
			                    (fn-lvls sym-int-alistp))
    :returns (new-lvls
	            sym-int-alistp
	            :hints (("Goal"
		                   :in-theory (disable assoc-equal-of-sym-int-alist)
		                   :use ((:instance assoc-equal-of-sym-int-alist
					                              (x fn) (y (sym-int-alist-fix fn-lvls)))))))
    (b* ((options (expand-options-fix options))
         ((expand-options o) options)
	       (fn-lvls (sym-int-alist-fix fn-lvls))
	       ((unless (symbolp fn)) fn-lvls)
	       (lvl (assoc-equal fn fn-lvls))
	       ((if lvl) (acons fn (1- (cdr lvl)) fn-lvls))
	       (fn-hint (assoc-equal fn o.functions))
	       ((if fn-hint)
	        (acons fn (1- (smt-function->depth (cdr fn-hint))) fn-lvls)))
      (acons fn 0 fn-lvls)))

  (define dont-expand ((fn acl2::any-p)
		                   (options expand-options-p)
		                   (fn-lvls sym-int-alistp))
    :returns (ok booleanp)
    (b* (((unless (symbolp fn)) nil)
	       (fn-lvls (sym-int-alist-fix fn-lvls))
	       (options (expand-options-fix options))
	       ((expand-options o) options)
	       (basic? (is-basic-function fn))
	       (types? (assoc-equal fn o.types))
	       (lvl (assoc-equal fn fn-lvls))
	       (functions? (assoc-equal fn o.functions)))
      (or (not (equal basic? nil))
	        (not (null types?))
	        (and lvl (<= (cdr lvl) 0))
	        (and (not lvl)
	             functions?
	             (<= (smt-function->depth (cdr functions?)) 0))))))

(defsection expand-term
  (pseudo-useless)

  (encapsulate nil ; adjust the theory a bit more for the defines expand-term
    (local (in-theory (enable pseudo-termp)))
    (local (in-theory (disable symbolp-of-fn-call-of-pseudo-termp
			                         pseudo-term-listp-of-symbol-listp
			                         acl2::symbol-listp-when-not-consp
			                         acl2::pseudo-termp-opener
			                         pairlis$
			                         acl2::pseudo-term-listp-cdr
			                         pseudo-term-listp-of-cdr-pseudo-termp-if
			                         default-car
			                         acl2::true-listp-of-car-when-true-list-listp
			                         true-list-listp
; the rest are added by mrg to make the measure proof faster (4.3s vs. 46s)
			                         acl2::subsetp-when-atom-right
			                         strip-cdrs
			                         default-cdr
			                         pseudo-term-sym-alistp-when-not-consp
			                         acl2::symbolp-of-car-when-symbol-listp
			                         consp-car-of-pseudo-term-sym-alist-fix
			                         acl2::subsetp-when-atom-left
			                         symbol-listp-of-car-when-symbol-list-listp
			                         member-equal
			                         null-of-pseudo-term-list-fix
			                         pseudo-termp-of-car-when-member-equal-of-pseudo-term-sym-alistp
			                         acl2::consp-of-symbol-list-fix
			                         symbol-list-listp-of-cdr-when-symbol-list-listp
			                         consp-when-member-equal-of-pseudo-term-sym-alistp)))

    (defines expand-term
      :well-founded-relation l<
      :flag-local nil
      :verify-guards nil
      :hints (("Goal" :in-theory (disable pseudo-termp pseudo-term-listp)))

      (define expand-term ((term pseudo-termp)
			                     (options expand-options-p)
			                     (fn-lvls sym-int-alistp)
			                     (alst pseudo-term-sym-alistp)
			                     (avoid symbol-listp)
			                     (clock natp)
			                     state)
	      :guard (and (subsetp-equal (acl2::simple-term-vars term) avoid)
		                (ptsa-avoid-p alst avoid))
	      :measure (list (nfix clock) 5
		                   (acl2-count (pseudo-term-fix term)))
	      :returns (mv (new-term pseudo-termp)
		                 (new-alst pseudo-term-sym-alistp)
		                 (new-avoid symbol-listp))
	      (b* (((mv ok-fix term-fix alst-fix avoid-fix)
	            (new-var-for-term-fix term alst avoid))
	           ((unless (mbt ok-fix)) (mv term-fix alst-fix avoid-fix))
	           (exist? (assoc-equal term alst))
	           ((if exist?) (mv (cdr exist?) alst avoid))
	           ((if (zp clock)) (mv term alst avoid))
	           ((unless (generate-freshvar term)) (mv term alst avoid))
	           ((cons fn actuals) term)
	           ((mv new-actuals alst-1 avoid-1)
	            (expand-term-list actuals options fn-lvls alst avoid clock state))
	           ((unless (mbt (equal (len new-actuals) (len actuals)))) (mv term alst avoid))
	           ((if (dont-expand fn options fn-lvls))
	            (mv (cons fn new-actuals) alst-1 avoid-1)))
	        (expand-term-1
	         (cons fn new-actuals) options fn-lvls alst-1 avoid-1 clock state)))

      (define expand-term-1 ((term pseudo-callp)
			                       (options expand-options-p)
			                       (fn-lvls sym-int-alistp)
			                       (alst pseudo-term-sym-alistp)
			                       (avoid symbol-listp)
			                       (clock posp)
			                       state)
	      :guard (and (subsetp-equal (acl2::simple-term-vars term) avoid)
		                (ptsa-avoid-p alst avoid))
	      :measure (list (nfix clock) 4
		                   (acl2-count (pseudo-term-fix term))
		                   )
	      :returns (mv (new-term pseudo-termp)
		                 (new-alst pseudo-term-sym-alistp)
		                 (new-avoid symbol-listp))
	      (b* (((mv ok-fix term-fix alst-fix avoid-fix)
	            (new-var-for-term-fix term alst avoid))
	           ((unless (mbt ok-fix)) (mv term-fix alst-fix avoid-fix))
	           ((unless (mbt (and (pseudo-callp term) (posp clock))))
	            (mv term alst avoid))
	           ((mv actual-vars alst-2 avoid-2)
	            (new-vars-for-term-list (cdr term) alst avoid)))
	        (expand-term-2
	         (cons (car term) actual-vars) options fn-lvls alst-2 avoid-2 clock state)))

      (define expand-term-2 ((term pseudo-callp)
			                       (options expand-options-p)
			                       (fn-lvls sym-int-alistp)
			                       (alst pseudo-term-sym-alistp)
			                       (avoid symbol-listp)
			                       (clock posp)
			                       state)
	      :guard (and (subsetp-equal (acl2::simple-term-vars term) avoid)
		                (ptsa-avoid-p alst avoid))
	      :measure (list (nfix clock) 3
		                   (acl2-count (pseudo-term-fix term)))
	      :returns (mv (new-term pseudo-termp)
		                 (new-alst pseudo-term-sym-alistp)
		                 (new-avoid symbol-listp))
	      (b* (((mv ok-fix term-fix alst-fix avoid-fix)
	            (new-var-for-term-fix term alst avoid))
	           ((unless (mbt ok-fix)) (mv term-fix alst-fix avoid-fix))
	           ((unless (mbt (and (pseudo-callp term) (posp clock))))
	            (mv term alst avoid))
	           ((mv ok substed-body) (function-substitution term state))
	           ((unless ok) (mv term alst avoid))
	           (new-lvls (update-fn-lvls (car term) options fn-lvls)))
	        (expand-term-3 substed-body options new-lvls alst avoid clock state)))

      (define expand-term-3 ((term pseudo-termp)
			                       (options expand-options-p)
			                       (fn-lvls sym-int-alistp)
			                       (alst pseudo-term-sym-alistp)
			                       (avoid symbol-listp)
			                       (clock posp)
			                       state)
	      :guard (and (subsetp-equal (acl2::simple-term-vars term) avoid)
		                (ptsa-avoid-p alst avoid))
	      :measure (list (nfix clock) 2
		                   (acl2-count (pseudo-term-fix term)))
	      :returns (mv (new-term pseudo-termp)
		                 (new-alst pseudo-term-sym-alistp)
		                 (new-avoid symbol-listp))
	      (b* (((mv ok-fix term-fix alst-fix avoid-fix)
	            (new-var-for-term-fix term alst avoid))
	           ((unless (mbt ok-fix)) (mv term-fix alst-fix avoid-fix))
	           ((unless (mbt (and (pseudo-termp term) (posp clock))))
	            (mv term alst avoid))
	           ((mv new-body alst-3 avoid-3)
	            (expand-term term options fn-lvls alst avoid (1- clock) state)))
	        (new-var-for-term new-body alst-3 avoid-3)))

      (define expand-term-list ((term-lst pseudo-term-listp)
				                        (options expand-options-p)
				                        (fn-lvls sym-int-alistp)
				                        (alst pseudo-term-sym-alistp)
				                        (avoid symbol-listp)
				                        (clock natp)
				                        state)
	      :guard (and (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid)
		                (ptsa-avoid-p alst avoid))
	      :measure (list (nfix clock) 5
		                   (acl2-count (pseudo-term-list-fix term-lst)))
	      :returns (mv (new-term-lst pseudo-term-listp)
		                 (new-alst pseudo-term-sym-alistp)
		                 (new-avoid symbol-listp))
	      (b* (((mv ok-fix term-lst-fix alst-fix avoid-fix)
	            (new-vars-for-term-list-fix term-lst alst avoid))
	           ((unless (mbt ok-fix)) (mv term-lst-fix alst-fix avoid-fix))
	           ((unless (consp term-lst)) (mv nil alst avoid))
	           ((cons term-hd term-tl) term-lst)
	           ((mv new-hd alst-1 avoid-1)
	            (expand-term term-hd options fn-lvls alst avoid clock state))
	           ((mv new-tl alst-2 avoid-2)
	            (expand-term-list term-tl options fn-lvls alst-1 avoid-1 clock state)))
	        (mv (cons new-hd new-tl) alst-2 avoid-2)))))

  (local (define cdr-induct-expand-term-list (term-lst options fn-lvls alst avoid clock state)
           :irrelevant-formals-ok t
           :verify-guards nil
           (b* (((if (atom term-lst)) nil)
	              ((mv & new-alst new-avoid)
	               (expand-term (car term-lst) options fn-lvls alst avoid clock state)))
             (cdr-induct-expand-term-list
              (cdr term-lst) options fn-lvls new-alst new-avoid clock state))))

  (defthm len-of-expand-term-list
    (equal (len (mv-nth 0 (expand-term-list term-lst options fn-lvls
					                                  alst avoid clock
					                                  state)))
	         (len term-lst))
    :hints (("Goal"
	           :expand((expand-term-list term-lst options fn-lvls alst avoid clock state))
	           :in-theory (enable expand-term-list cdr-induct-expand-term-list)
	           :induct (cdr-induct-expand-term-list term-lst options fn-lvls alst
						                                      avoid clock state))))


  (defsection expand-term.an-exercise-in-macro-writing
; Breaking expand-term into four pieces makes the subsequent proofs *way*
; easier to debug (and they exeucte faster).  But, it's tedious to state
; the same theorem four times (for expand-term, expand-term-1,
; expand-term-2 and expand-term-3.  The defthm-expand-term* takes the
; defthm with :flag expand-term and makes copies for the other three
; functions.
    (defun expand-term-map (thm-name suffix)
      (b* (((unless suffix) nil)
	         (new-name (intern-in-package-of-symbol
		                  (coerce (append (explode-atom thm-name 10)
				                              (cons #\- (explode-atom suffix 10)))
			                        'acl2::string)
		                  thm-name))
	         (f-name (intern-in-package-of-symbol
		                (coerce (append (explode-atom 'expand-term 10)
				                            (cons #\- (explode-atom suffix 10)))
			                      'acl2::string)
		                thm-name)))
	      (acons thm-name new-name
	             (acons 'expand-term f-name nil))))

    (defun expand-term-maps (thm-name suffixes)
      (if (endp suffixes) nil
	      (cons (expand-term-map thm-name (car suffixes))
	            (expand-term-maps thm-name (cdr suffixes)))))

    (defun expand-term-replace (x m)
      (cond ((consp x)
	           (cons (expand-term-replace (car x) m)
		               (expand-term-replace (cdr x) m)))
	          ((assoc-equal x m)
	           (cdr (assoc-equal x m)))
	          (t x)))

    (defun expand-term-thms (thm maps)
      (if (endp maps) nil
	      (cons (expand-term-replace thm (car maps))
	            (expand-term-thms thm (cdr maps)))))

    (defun expand-term-thm (thms)
      (b* (((unless (consp thms)) nil)
	         ((cons thm-hd thm-tl) thms)
	         ((unless (and (consp thm-hd) (equal (car thm-hd) 'defthm)))
	          (cons thm-hd (expand-term-thm thm-tl)))
	         (flg (member-equal :flag thm-hd))
	         ((unless (and flg (equal (cadr flg) 'expand-term)))
	          (cons thm-hd (expand-term-thm thm-tl)))
	         (thms-hd (expand-term-thms
		                 thm-hd (expand-term-maps (cadr thm-hd)
					                                    (list nil #\1 #\2 #\3)))))
	      (append thms-hd (expand-term-thm thm-tl))))

    (defmacro defthm-expand-term* (&rest thms)
      (cons 'defthm-expand-term-flag (expand-term-thm thms))))

  (defthm-expand-term*
    (defthm expand-term-avoid-grows
      (implies (symbol-listp avoid)
	             (subsetp-equal avoid
		                          (mv-nth 2 (expand-term term options fn-lvls alst avoid clock state))))
      :hints('(
	             :expand((expand-term term options fn-lvls alst avoid clock state)
		                   (expand-term term options fn-lvls alst avoid 0 state))))
      :flag expand-term)
    (defthm expand-term-list-avoid-grows
      (implies (symbol-listp avoid)
	             (subsetp-equal avoid
		                          (mv-nth 2
		                                  (expand-term-list term-lst options fn-lvls alst avoid clock state))))
      :hints('(
	             :expand (
	                      (expand-term-list term-lst options fn-lvls alst avoid clock state)
	                      (expand-term-list nil options fn-lvls alst avoid clock state))))
      :flag expand-term-list))

  (defthm-expand-term*
    (defthm expand-term-ptsa-avoid
      (ptsa-avoid-p (mv-nth 1 (expand-term term options fn-lvls alst avoid clock state))
		                (mv-nth 2 (expand-term term options fn-lvls alst avoid clock state)))
      :hints('(
	             :expand((expand-term term options fn-lvls alst avoid clock state)
		                   (expand-term term options fn-lvls alst avoid 0 state))
	             :in-theory (disable new-var-for-term-fix-ensures-ptsa-avoid)
	             :use((:instance new-var-for-term-fix-ensures-ptsa-avoid))))
      :flag expand-term)
    (defthm expand-term-list-ptsa-avoid
      (ptsa-avoid-p (mv-nth 1 (expand-term-list term-lst options fn-lvls alst avoid clock state))
		                (mv-nth 2 (expand-term-list term-lst options fn-lvls alst avoid clock state)))
      :hints('(
	             :expand (
	                      (expand-term-list term-lst options fn-lvls alst avoid clock state)
	                      (expand-term-list nil options fn-lvls alst avoid clock state))
	             :in-theory (disable new-vars-for-term-list-fix-ensures-ptsa-avoid)
	             :use((:instance  new-vars-for-term-list-fix-ensures-ptsa-avoid))))
      :flag expand-term-list))

  (defthm-expand-term*
    (defthm expand-term-new-avoid-3
      (implies (and (pseudo-termp term)
		                (symbol-listp avoid)
		                (subsetp-equal (acl2::simple-term-vars term) avoid))
	             (subsetp-equal
		            (acl2::simple-term-vars (mv-nth 0 (expand-term term options fn-lvls alst avoid clock state)))
		            (mv-nth 2 (expand-term term options fn-lvls alst avoid clock state))))
      :hints('(
	             :expand((expand-term term options fn-lvls alst avoid clock state)
		                   (expand-term term options fn-lvls alst avoid 0 state))))
      :flag expand-term)
    (defthm expand-term-list-new-avoid-3
      (implies (and (pseudo-term-listp term-lst)
		                (symbol-listp avoid)
		                (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid))
	             (subsetp-equal
		            (acl2::simple-term-vars-lst (mv-nth 0 (expand-term-list term-lst options fn-lvls alst avoid clock state)))
		            (mv-nth 2 (expand-term-list term-lst options fn-lvls alst avoid clock state))))
      :hints('(
	             :expand (
	                      (expand-term-list term-lst options fn-lvls alst avoid clock state)
	                      (expand-term-list nil options fn-lvls alst avoid clock state))))
      :flag expand-term-list)
    :hints(("Goal"
	          :in-theory (e/d (acl2::simple-term-vars acl2::simple-term-vars-lst)
			                      (cdr-assoc-when-ptsa-avoid-p)))))

  (defthm verify-guards-lemma-1
    (implies (and (pseudo-callp term) (not (symbolp (car term))))
	           (equal (caar term) 'lambda))
    :hints(("Goal" :use ((:instance pseudo-lambdap (acl2::x (car term)))))))

  (verify-guards expand-term
    :hints(("Goal"
            :in-theory (enable acl2::simple-term-vars acl2::simple-term-vars-lst))))

  (defthm-expand-term*
    (defthm expand-term-preserves-ev-smtcp
      (implies (and (pseudo-termp term)
		                (ptsa-avoid-p alst avoid)
		                (alistp env)
		                (subsetp-equal (acl2::simple-term-vars term) avoid)
		                (pseudo-termp x)
		                (subsetp-equal (acl2::simple-term-vars x) avoid))
	             (mv-let (new-term new-alst new-avoid)
		             (expand-term term options fn-lvls alst avoid clock state)
		             (declare (ignore new-term new-avoid))
		             (equal (ev-smtcp x (new-env new-alst env))
			                  (ev-smtcp x (new-env alst env)))))
      :hints('(
	             :expand(
	                     (expand-term term options fn-lvls alst avoid clock state)
	                     (expand-term term options fn-lvls alst avoid 0 state))))
      :flag expand-term)

    (defthm expand-term-list-preserves-ev-smtcp
      (implies (and (pseudo-term-listp term-lst)
		                (ptsa-avoid-p alst avoid)
		                (alistp env)
		                (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid)
		                (pseudo-termp x)
		                (subsetp-equal (acl2::simple-term-vars x) avoid))
	             (mv-let (new-term-lst new-alst new-avoid)
		             (expand-term-list term-lst options fn-lvls alst avoid clock state)
		             (declare (ignore new-term-lst new-avoid))
		             (equal (ev-smtcp x (new-env new-alst env))
			                  (ev-smtcp x (new-env alst env)))))
      :hints('(
	             :expand (
	                      (expand-term-list term-lst options fn-lvls alst avoid clock state)
	                      (expand-term-list nil options fn-lvls alst avoid clock state))))
      :flag expand-term-list)
    :hints(
           ("Goal"
	          :in-theory (enable acl2::simple-term-vars acl2::simple-term-vars-lst))))

  (defthm-expand-term*
    (defthm expand-term-preserves-ev-smtcp-lst
      (implies (and (pseudo-termp term)
		                (ptsa-avoid-p alst avoid)
		                (alistp env)
		                (subsetp-equal (acl2::simple-term-vars term) avoid)
		                (pseudo-term-listp xlst)
		                (subsetp-equal (acl2::simple-term-vars-lst xlst) avoid))
	             (mv-let (new-term new-alst new-avoid)
		             (expand-term term options fn-lvls alst avoid clock state)
		             (declare (ignore new-term new-avoid))
		             (equal (ev-smtcp-lst xlst (new-env new-alst env))
			                  (ev-smtcp-lst xlst (new-env alst env)))))
      :hints('(
	             :expand(
	                     (expand-term term options fn-lvls alst avoid clock state)
	                     (expand-term term options fn-lvls alst avoid 0 state))))
      :flag expand-term)

    (defthm expand-term-list-preserves-ev-smtcp-lst
      (implies (and (pseudo-term-listp term-lst)
		                (ptsa-avoid-p alst avoid)
		                (alistp env)
		                (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid)
		                (pseudo-term-listp xlst)
		                (subsetp-equal (acl2::simple-term-vars-lst xlst) avoid))
	             (mv-let (new-term-lst new-alst new-avoid)
		             (expand-term-list term-lst options fn-lvls alst avoid clock state)
		             (declare (ignore new-term-lst new-avoid))
		             (equal (ev-smtcp-lst xlst (new-env new-alst env))
			                  (ev-smtcp-lst xlst (new-env alst env)))))
      :hints('(
	             :expand (
	                      (expand-term-list term-lst options fn-lvls alst avoid clock state)
	                      (expand-term-list nil options fn-lvls alst avoid clock state))))
      :flag expand-term-list)
    :hints(
           ("Goal"
	          :in-theory (enable new-var-for-term-fix new-vars-for-term-list-fix
			                         acl2::simple-term-vars acl2::simple-term-vars-lst))))

  (encapsulate nil
; We are now so close to proving the correctness of expand-term and
; expand-term-list.  But, there's one subgoal left to handle.
; In English, if alst maps term to freshvar, we need to show
;   (equal (ev-smtcp freshvar (new-env alst env))
;          (ev-smtcp term (new-env alst env)))
; Seems "obvious", but we need to show that bindings in the prefix of alst
; before the one for term don't affect free variables in term or freshvar.
; This follows from the constraints of ptsa-avoid-p, but we need to take
; ACL2 by the hand and slowly walk step-by-step through the process.
    (defthm base-case-lemma
      (implies (and (alistp env)
		                (symbolp s)
		                (pseudo-termp term)
		                (not (member-equal s (acl2::simple-term-vars term))))
	             (equal (cdr (assoc-equal s (new-env (cons (cons term s) nil) env)))
		                  (ev-smtcp term (new-env (cons (cons term s) nil) env))))
      :hints(("Goal"
	            :in-theory (e/d (new-env intersectp-equal) (ev-smtcp-fresh-bindings))
	            :use(
	                 (:instance ev-smtcp-fresh-bindings
			                        (alst (cons (cons term s) nil))
			                        (avoid (acl2::simple-term-vars term)))))))

    (defthm base-case
      (implies (and (ptsa-avoid-p alst avoid)
		                (assoc-equal term alst)
		                (equal term (car (car alst))))
	             (equal (cdr (assoc-equal (cdr (assoc-equal term alst))
					                              (new-env alst env)))
		                  (ev-smtcp term (new-env alst env))))
      :hints(("Goal"
	            :in-theory (e/d (ptsa-avoid-p new-env acl2::simple-term-vars-lst)
			                        (base-case-lemma))
	            :use(
	                 (:instance base-case-lemma (env (new-env (cdr alst) env))
				                      (s (cdar alst))
				                      (term (caar alst)))))))

    (defthm induct-ev-smtcp-of-term-lemma-1
      (implies (assoc-equal term alst)
	             (subsetp-equal (acl2::simple-term-vars term)
			                        (acl2::simple-term-vars-lst (strip-cars alst))))
      :hints(("Goal" :in-theory (enable acl2::simple-term-vars-lst))))

    (defthm induct-ev-smtcp-of-term-lemma-2
      (implies (and (ptsa-avoid-p alst avoid)
		                (assoc-equal term alst))
	             (not (member-equal (cdar alst)
				                          (acl2::simple-term-vars term))))
      :rule-classes ((:rewrite :match-free :all))
      :hints(("Goal" :expand ((ptsa-avoid-p alst avoid)))))

    (defthm pseudo-termp-of-car-of-assoc-equal-when-ptsa-avoid-p
      (implies (and (ptsa-avoid-p alst avoid)
		                (assoc-equal term alst))
	             (pseudo-termp term))
      :hints(("Goal" :expand (ptsa-avoid-p alst avoid))))

    (defthmd induct-ev-smtcp-of-term
      (implies (and (ptsa-avoid-p alst avoid)
		                (assoc-equal term alst)
		                (alistp env)
		                (not (equal term (car (car alst)))))
	             (equal (ev-smtcp term (new-env alst env))
		                  (ev-smtcp term (new-env (cdr alst) env))))
      :hints(("Goal"
	            :in-theory (e/d (new-env intersectp-equal) (ev-smtcp-fresh-bindings))
	            :use(
	                 (:instance ev-smtcp-fresh-bindings
			                        (alst (cons (car alst) nil))
			                        (avoid (acl2::simple-term-vars term))
			                        (env (new-env (cdr alst) env)))))))

    (defthm induct-assoc-of-freshvar-lemma-1
      (implies
	     (AND (alistp alst)
	          (assoc-equal term alst))
	     (member-equal (cdr (assoc-equal term alst))
		                 (strip-cdrs alst))))

    (defthmd induct-assoc-of-freshvar-lemma-2
      (IMPLIES
	     (and (ptsa-avoid-p alst avoid)
	          (assoc-equal term alst)
	          (not (equal term (caar alst))))
	     (not (equal (cdr (assoc-equal term alst)) (cdar alst))))
      :hints(("Goal"
	            :expand ((ptsa-avoid-p alst avoid)))))

    (defthmd induct-assoc-of-freshvar
      (implies (and (ptsa-avoid-p alst avoid)
		                (assoc-equal term alst)
		                (not (equal term (caar alst))))
	             (equal (cdr (assoc-equal (cdr (assoc-equal term alst))
					                              (new-env alst env)))
		                  (cdr (assoc-equal (cdr (assoc-equal term (cdr alst)))
					                              (new-env (cdr alst) env)))))
      :hints(("Goal"
	            :expand ((new-env alst env))
	            :use((:instance induct-assoc-of-freshvar-lemma-2)))))

    (defthm induction-step
      (implies (and (ptsa-avoid-p alst avoid)
		                (assoc-equal term alst)
		                (alistp env)
		                (not (equal term (caar alst)))
		                (equal (cdr (assoc-equal (cdr (assoc-equal term (cdr alst)))
					                                   (new-env (cdr alst) env)))
			                     (ev-smtcp term (new-env (cdr alst) env))))
	             (equal (cdr (assoc-equal (cdr (assoc-equal term alst))
				                                (new-env alst env)))
	                    (ev-smtcp term (new-env alst env))))
      :hints(("Goal"
              :in-theory (disable induct-ev-smtcp-of-term
			                            induct-assoc-of-freshvar)
              :use((:instance induct-ev-smtcp-of-term)
	                 (:instance induct-assoc-of-freshvar)))))

    (defthm correctness-of-expand-term-lemma-*1/1.2
      (implies
	     (and (assoc-equal term alst)
	          (pseudo-termp term)
	          (ptsa-avoid-p alst avoid)
	          (alistp env))
	     (equal (cdr (assoc-equal (cdr (assoc-equal term alst))
				                        (new-env alst env)))
	            (ev-smtcp term (new-env alst env))))
      :hints(
; OK, I give up.  I try to avoid hinting subgoals, but I can't find a
; way to get ACL2 to find the base-case and induction-step lemmas
; automatically.  I suspect the problem is because of avoid is 'free'
; in those lemmas.  I could write an alternative to psta-avoid-p that
; doesn't use avoid, but I expect that this will all become simpler
; when I change how fresh-variables are created.  So, I'll give up
; and provide subgoal hints for now.
	           ("Subgoal *1/2"
	            :in-theory (disable base-case)
	            :use((:instance base-case)))
	           ("Subgoal *1/5"
	            :in-theory (disable induction-step)
	            :use((:instance induction-step))))))

  (defthm-expand-term*
    (defthm correctness-of-expand-term
      (implies (and (ev-smtcp-meta-extract-global-facts)
		                (pseudo-termp term)
		                (ptsa-avoid-p alst avoid)
		                (alistp env)
		                (subsetp-equal (acl2::simple-term-vars term) avoid))
	             (mv-let (new-term new-alst new-avoid)
		             (expand-term term options fn-lvls alst avoid clock state)
		             (declare (ignore new-avoid))
		             (equal (ev-smtcp new-term (new-env new-alst env))
			                  (ev-smtcp term (new-env alst env)))))
      :hints('(
	             :expand(
	                     (expand-term term options fn-lvls alst avoid clock state)
	                     (expand-term term options fn-lvls alst avoid 0 state))
               ))
      :flag expand-term)

    (defthm correctness-of-expand-term-list
      (implies (and (ev-smtcp-meta-extract-global-facts)
		                (pseudo-term-listp term-lst)
		                (ptsa-avoid-p alst avoid)
		                (alistp env)
		                (subsetp-equal (acl2::simple-term-vars-lst term-lst) avoid))
	             (mv-let (new-term-lst new-alst new-avoid)
		             (expand-term-list term-lst options fn-lvls alst avoid clock state)
		             (declare (ignore  new-avoid))
		             (equal (ev-smtcp-lst new-term-lst (new-env new-alst env))
			                  (ev-smtcp-lst term-lst (new-env alst env)))))
      :hints('(
	             :expand (
	                      (expand-term-list term-lst options fn-lvls alst avoid clock state)
	                      (expand-term-list nil options fn-lvls alst avoid clock state))))
      :flag expand-term-list)
    :hints(
           ("Goal" :in-theory (enable ev-smtcp-of-fncall-args
				                              acl2::simple-term-vars
				                              acl2::simple-term-vars-lst)))))


(defsection generate-equalities
  (pseudo-useless)

  (define generate-equalities ((alst pseudo-term-sym-alistp))
    :returns (res pseudo-termp)
    :measure (len alst)
    (b* (((unless (mbt (pseudo-term-sym-alistp alst))) ''t)
	       ((unless (consp alst)) ''t)
	       ((cons alst-hd alst-tl) alst)
	       ((cons term var) alst-hd))
      `(if (equal ,var ,term)
	         ,(generate-equalities alst-tl)
	       'nil))
    ///
    (more-returns
     (res :name simple-term-vars-of-generate-equalities
	        (implies (ptsa-avoid-p alst avoid)
		               (acl2::set-equiv (acl2::simple-term-vars res)
				                            (union-equal (acl2::simple-term-vars-lst (strip-cars alst))
					                                       (strip-cdrs alst))))
	        :hints(
	               ("Goal"
	                :in-theory (enable generate-equalities
			                               acl2::simple-term-vars
			                               acl2::simple-term-vars-lst
			                               ptsa-avoid-p))))))

; I'm tired.  The following proof is very brute force.
; I plan to write nicer proof when I redo new-fresh-var and all that stuff.
  (local (defthmd lemma-*1/3
           (IMPLIES (AND (CONSP ALST)
		                     (EV-SMTCP (GENERATE-EQUALITIES (CDR ALST))
			                             (NEW-ENV (CDR ALST) ENV))
		                     (PTSA-AVOID-P ALST AVOID)
		                     (ALISTP ENV))
	                  (EV-SMTCP (GENERATE-EQUALITIES ALST)
		                          (NEW-ENV ALST ENV)))
           :hints(
                  ("Goal"
                   :expand ((generate-equalities alst)
	                          (ptsa-avoid-p alst avoid))
                   :in-theory (e/d (acl2::simple-term-vars-lst intersectp-equal new-env)
		                               (ev-smtcp-fresh-bindings))
                   :use(
                        (:instance ev-smtcp-fresh-bindings
		                               (alst (list (car alst)))
		                               (term (caar alst))
		                               (avoid (acl2::simple-term-vars (caar alst)))
		                               (env (new-env (cdr alst) env)))
                        (:instance ev-smtcp-fresh-bindings
		                               (alst (list (car alst)))
		                               (term (generate-equalities (cdr alst)))
		                               (avoid (acl2::simple-term-vars (generate-equalities (cdr alst))))
		                               (env (new-env (cdr alst) env))))))))

  (defthm correctness-of-generate-equalities
    (implies (and (ptsa-avoid-p alst avoid)
		              (alistp env))
	           (ev-smtcp (generate-equalities alst)
		                   (new-env alst env)))
    :hints(
           ("Goal" :in-theory (enable generate-equalities new-env))
           ("Subgoal *1/3" :use((:instance lemma-*1/3)))))

  (defthm generate-equalities-of-expand-term
    (implies
     (alistp env)
     (ev-smtcp
	    (generate-equalities (mv-nth 1 (expand-term term options fn-lvls alst avoid clock state)))
	    (new-env (mv-nth 1 (expand-term term options fn-lvls alst avoid clock state))
		           env)))
    :hints(("Goal"
            :in-theory (disable correctness-of-generate-equalities)
            :use((:instance correctness-of-generate-equalities
		                        (alst  (mv-nth 1 (expand-term term options fn-lvls
                                                          alst avoid clock state)))
		                        (avoid (mv-nth 2 (expand-term term options fn-lvls
                                                          alst avoid clock state)))))))))

(defsection expand-cp
  (pseudo-useless)

  (define expand-cp-fn ((cl pseudo-term-listp) (hints smtlink-hint-p) state)
    :returns (mv (new-goal pseudo-termp) (alst pseudo-term-sym-alistp))
    :guard-hints(("Goal" :expand ((:free (avoid) (ptsa-avoid-p nil avoid)))))
    (b* (((unless (mbt (and (pseudo-term-listp cl)
			                      (smtlink-hint-p hints))))
	        (mv (disjoin (pseudo-term-list-fix cl)) nil))
         (options (construct-expand-options hints))
	       ((expand-options o) options)
	       (goal (disjoin cl))
	       ((mv new-goal alst &)
	        (expand-term goal o nil nil (acl2::simple-term-vars goal)
		                   o.wrld-fn-len state)))
      (mv `(if ,(generate-equalities alst) ,new-goal 't) alst)))

  (defthm correctness-of-expand-cp-fn
    (implies
     (and (ev-smtcp-meta-extract-global-facts)
	        (pseudo-term-listp cl)
	        (alistp env))
     (mv-let (new-goal alst)
	     (expand-cp-fn cl hints state)
	     (equal
		    (ev-smtcp new-goal (new-env alst env))
		    (ev-smtcp (disjoin cl) env))))
    :hints(("Goal"
            :expand ((expand-cp-fn cl hints state)
	                   (:free (avoid) (ptsa-avoid-p nil avoid))))))

  (defthm expand-cp-fn-bad-hints
    (implies (not (smtlink-hint-p hints))
	           (not (mv-nth 1 (expand-cp-fn cl hints state))))
    :hints(("Goal" :expand ((expand-cp-fn cl hints state)))))

  (define expand-cp ((cl pseudo-term-listp)
		                 (hints t)
		                 state)
    :guard-hints(("Goal" :expand((:free (avoid) (ptsa-avoid-p nil avoid)))))
    (b* (((unless (smtlink-hint-p hints)) (value (list cl)))
         (cl (pseudo-term-list-fix cl))
         ((mv new-goal &) (expand-cp-fn cl hints state))
         (next-cp (cdr (assoc-equal 'expand *SMT-architecture*)))
         ((if (null next-cp)) (value (list cl)))
         (the-hint `(:clause-processor (,next-cp clause ',hints state))))
      (value (list `((hint-please ',the-hint) ,new-goal)))))

  (defthm disjoin-of-singleton
    (equal (disjoin (list x)) x)
    :hints(("Goal" :expand ((disjoin (list x))))))

  (defthm correctness-of-expand-cp
    (implies
     (and (ev-smtcp-meta-extract-global-facts)
	        (pseudo-term-listp cl)
	        (alistp env)
	        (ev-smtcp (conjoin-clauses (acl2::clauses-result (expand-cp cl hints state)))
		                (new-env (mv-nth 1 (expand-cp-fn cl hints state)) env)))
     (ev-smtcp (disjoin cl) env))
    :hints (("Goal" :in-theory (enable expand-cp)))
    :rule-classes :clause-processor))
