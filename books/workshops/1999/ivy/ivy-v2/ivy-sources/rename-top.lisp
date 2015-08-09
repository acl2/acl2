(in-package "ACL2")

;; Function (rename-all f), defined in book "rename", renames
;; all bound variables.
;;
;; This book brings together the three rename books.

(include-book "rename")

;;-----------------------------------

(encapsulate
 nil

 (local (include-book "rename-sound"))

 ;; This event is redundant.  Its occurrence here makes it global.

 (defthm rename-all-fsound
   (equal (feval (rename-all f) i)
	  (feval f i)))
 )

;;-----------------------------------

(encapsulate
 nil

 (local (include-book "rename-unique"))

 ;; This event is redundant.  Its occurrence here makes it global.

 (defthm rename-all-setp-qvars
   (setp (quantified-vars (rename-all f))))

 )

;;-----------------------------------

;; rename-all is nonrecursive, and we have to disable it
;; so the preceding results can be used.

(in-theory (disable rename-all))

