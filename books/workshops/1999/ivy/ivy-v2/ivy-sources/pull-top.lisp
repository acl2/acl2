(in-package "ACL2")

;; Function pull-quants pulls quantifiers to the top of a formula.
;; Here we gather the definitions and top lemmas.

(include-book "pull")

;;-----------------------------------

(encapsulate
 nil

 (local (include-book "pull-sound"))

 ;; This event is redundant.  Its occurrence here makes it global.

 (defthm pull-quants-fsound
   (equal (feval (pull-quants f) i)
	  (feval f i)))
 )

;;-----------------------------------

(encapsulate
 nil

 (local (include-book "pull-pulls"))

 ;; These events are redundant.  Their occurrences here make them global.

 (defthm pull-quants-pulls
   (implies (and (nnfp f)
		 (setp (quantified-vars f))
		 (not (free-vars f)))
	    (quantifier-free (remove-leading-quants (pull-quants f)))))

 (defthm pull-quants-pulls-2
   (implies (and (nnfp f)
		 (not (free-vars f))
		 (setp (quantified-vars f))
		 (equal (exists-count f) 0))
	    (universal-prefix-nnf (pull-quants f))))
 )

;;-----------------------------------
;; Pull-quants is nonrecursive---we have to disable it
;; so the preceding results can be used.

(in-theory (disable pull-quants))
