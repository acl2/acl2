; cp-more.lisp:  some theorems about functions in [books]/clause-processors.
; Copyright (C) 2021, University of British Columbia
;
; License: A 3-clause BSD license.
; See the LICENSE file distributed with ACL2
;
; Original author: Mark Greenstreet <mrg@cs.ubc.ca>

(in-package "ACL2")

(include-book "std/lists/sets" :dir :system)
(include-book "clause-processors/term-vars" :dir :system)
(include-book "clause-processors/unify-subst" :dir :system)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theorems about simple-term-vars and simple-term-vars-lst               ;;
;;   (from [books]/clause-processors/term-vars.lisp)                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro pseudo-useless nil
  '(local (in-theory (disable pseudo-termp acl2::pseudo-termp-opener))))

(local (pseudo-useless))

(defthm simple-term-vars-of-symbol
  (implies (and (symbolp s) s)
	   (equal (acl2::simple-term-vars s) (list s)))
  :hints(("Goal"
    :in-theory (enable acl2::simple-term-vars))))


(defthm simple-term-vars-of-term-list-1
  (subsetp-eq (acl2::simple-term-vars (car term-lst))
		   (acl2::simple-term-vars-lst term-lst))
  :hints(("Goal" :in-theory (enable acl2::simple-term-vars-lst))))

(defthm simple-term-vars-of-term-list-2
  (subsetp-eq (acl2::simple-term-vars-lst (cdr term-lst))
	     (acl2::simple-term-vars-lst term-lst))
  :hints(("Goal" :in-theory (enable acl2::simple-term-vars-lst))))

(defthm simple-term-vars-of-assoc
  (implies (subsetp-equal (simple-term-vars-lst (strip-cdrs al)) vars)
           (subsetp-equal (simple-term-vars (cdr (assoc-equal sym al))) vars))
  :hints(("Goal"
    :in-theory (enable simple-term-vars-lst))))

(defthm simple-term-vars-of-pairlis$
  (subsetp-equal (simple-term-vars-lst (strip-cdrs (pairlis$ k v)))
                 (simple-term-vars-lst v))
  :hints(("Goal" :in-theory (enable simple-term-vars-lst))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theorems about functions from [books]/clause-processors/term-vars.lisp)  ;;
;;     (esp. wrt. simple-term-vars)                                         ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm simple-term-vars-of-unify-const
  (subsetp-eq (simple-term-vars-lst (strip-cdrs (mv-nth 1 (unify-const pat const alist))))
              (simple-term-vars-lst (strip-cdrs alist)))
  :hints(("Goal"
    :in-theory (enable unify-const simple-term-vars simple-term-vars-lst))))
            
(defthm-simple-one-way-unify-flag
    simple-term-vars-of-simple-one-way-unify
  (defthm simple-term-vars-of-simple-one-way-unify
    (implies (and (pseudo-termp term)
                  (pseudo-termp pat)
		  (alistp alst)
		  (symbol-listp all-vars)
		  (subsetp-equal (simple-term-vars term)
				 all-vars)
		  (subsetp-equal (simple-term-vars-lst (strip-cdrs alst))
				 all-vars))
	     (mv-let (ok new-alst)
	             (simple-one-way-unify pat term alst)
		     (if ok
		         (subsetp-equal (simple-term-vars-lst (strip-cdrs new-alst))
			                all-vars)
			 t)))
    :flag simple-one-way-unify)
  (defthm simple-term-vars-of-simple-one-way-unify-lst
    (implies (and (pseudo-term-listp term)
                  (pseudo-term-listp pat)
		  (alistp alst)
		  (symbol-listp all-vars)
		  (subsetp-equal (simple-term-vars-lst term)
				 all-vars)
		  (subsetp-equal (simple-term-vars-lst (strip-cdrs alst))
				 all-vars))
	     (mv-let (ok new-alst)
	             (simple-one-way-unify-lst pat term alst)
		     (if ok
		         (subsetp-equal (simple-term-vars-lst (strip-cdrs new-alst))
			                all-vars)
			 t)))
    :flag simple-one-way-unify-lst)
  :hints (("Goal" :induct (simple-one-way-unify-flag flag pat term alst)
    :in-theory (enable simple-one-way-unify simple-one-way-unify-lst
                        simple-term-vars simple-term-vars-lst))))

(defthm-substitute-into-term-flag
    simple-term-vars-of-substitute-into-term
  (defthm simple-term-vars-of-substitute-into-term
    (subsetp-equal (simple-term-vars (acl2::substitute-into-term x al))
                   (simple-term-vars-lst (strip-cdrs al)))
  :flag substitute-into-term)
  (defthm simple-term-vars-of-substitute-into-list
    (subsetp-equal (simple-term-vars-lst (acl2::substitute-into-list x al))
                   (simple-term-vars-lst (strip-cdrs al)))
  :flag substitute-into-list)
  :hints (("Goal" :induct (substitute-into-term-flag flag x al)
    :in-theory (enable substitute-into-term substitute-into-list
                        simple-term-vars simple-term-vars-lst))))

