(in-package "BAG")

(include-book "meta")

(in-theory
 (disable
  (:REWRITE SUBBAGP-IMPLIES-REMOVE-BAG)
  (:REWRITE REMOVE-BAG-CONS-REMOVE-1-NOT-EQUAL)
  (:REWRITE REMOVE-BAG-REMOVE-1)
  (:REWRITE REMOVE-BAG-CONS)
  (:REWRITE SUBBAGP-CDR)
  (:REWRITE SUBBAGP-IMPLIES-COMMON-MEMBERS-ARE-IRRELEVANT)
;  (:REWRITE NOT-REMOVE-BAG-IMPLIES-NOT-REMOVE-BAG-REMOVE-1)
  (:REWRITE SUBBAGP-APPEND-APPEND)
  (:REWRITE SUBBAGP-APPEND-APPEND-LEFT)
  (:REWRITE SUBBAGP-IMPLIES-SUBBAGP-CONS)
  (:REWRITE MEMBERSHIP-EXTRACTION-INSTANCE)
  ))

(in-theory
 (disable
  (:REWRITE *TRIGGER*-UNIQUE-SUBBAGPS-IMPLIES-DISJOINTNESS)
  (:REWRITE *TRIGGER*-SUBBAGP-PAIR-DISJOINT) ;can we get rid of this then?
 ))

;we look through HYPS for a term of the form (subbagp x y)
;if such an item is found, we return (mv t y).  else, we return (mv nil nil)
;what if multple such things might be found?
(defun find-exact-subbagp-instance (x hyps)
  (declare (type t hyps)
           )
  (if (consp hyps)
      (let ((entry (car hyps)))
	(if (and (consp entry)
		 ; (not (subbagp term zed))
		 (equal (car entry) 'not)
		 (consp (cdr entry))
		 (consp (cadr entry))
		 (equal (car (cadr entry)) 'subbagp)
		 (consp (cdr (cadr entry)))
		 (equal (cadr (cadr entry)) x)
		 (consp (cddr (cadr entry))))
	    (mv t (caddr (cadr entry)))
	  (find-exact-subbagp-instance x (cdr hyps))))
    (mv nil nil)))

;look through HYPS for a term of the form (subbagp term zed) where x is a
;syntactic subbagp of TERM.  if such a term is found, return (mv t term zed
;rh) where rh contains the remainder of HYPS (the stuff not yet processed by
;this function) else, return (mv nil nil nil nil)

(defun find-syntax-subbagp-instance (x hyps)
  (declare (type t hyps)
           (xargs :guard (and (PSEUDO-TERM-LISTP hyps)
                              (PSEUDO-TERMP X)))
           )
  (if (consp hyps)
      (let ((entry (car hyps)))
	(let ((hit ;(not (subbagp term zed))
	       (and
		(consp entry)
		(equal (car entry) 'not)
		(consp (cdr entry))
		(consp (cadr entry))
		(equal (car (cadr entry)) 'subbagp) ;;(subbagp term zed)
		(consp (cdr (cadr entry)))
		(consp (cddr (cadr entry)))
		(let ((term (cadr (cadr entry)))
		      (zed (caddr (cadr entry))))
		  (and (syntax-subbagp-fn nil x term)
		       (cons term zed))))))
	  (if hit
	      (mv t (car hit) (cdr hit) (cdr hyps))
	    (find-syntax-subbagp-instance x (cdr hyps)))))
    (mv nil nil nil nil)))

;n seems to be a counter which restricts the amount of looking we do (hence the "bounded" in the function name).
(defun find-bounded-subbagp-path (top x rh y hyps n res)
  (declare (type (integer 0 *) n)
	   (xargs :guard (and (PSEUDO-TERM-LISTP hyps) ;i'm not sure all the guards are necessary, but they worked!
                              (PSEUDO-TERM-LISTP rh)
                              (PSEUDO-TERMP X)
                              (PSEUDO-TERMP y))
                  :measure (nfix n)))
  (if (zp n)
      nil
    (if (and top (equal x y))
        (cons (cons y t) res)
      (if (and top (syntax-subbagp-fn nil x y))
          (cons (cons y nil) res)
        (met ((hit x0) (if top (find-exact-subbagp-instance x rh) (mv nil nil)))
             (or (and hit (find-bounded-subbagp-path t x0 hyps y hyps (1- n) (cons (cons x0 t) res)))
                 (met ((hit x0 x1 nrh) (find-syntax-subbagp-instance x rh))
                      (and hit
                           (or (find-bounded-subbagp-path t   x1 hyps y hyps (1- n) (cons (cons x1 t) (cons (cons x0 nil) res)))
                               (find-bounded-subbagp-path nil x  nrh  y hyps (1- n) res))))))))))

(defun reverse-path (path res)
  (declare (type t path res))
  (if (consp path)
      (let ((entry (car path)))
	(and (consp entry)
	     (let ((res `(cons (cons ,(car entry) (quote ,(cdr entry))) ,res)))
	       (reverse-path (cdr path) res))))
    res))

;what does this do?
;we look through HYPS for a term of the form (subbagp x BLAH)
;if such an item is found, we test whether BLAH equals y.  else, we return nil
;what if multple such things might be found?
(defun subbagp-instance (x y hyps)
  (declare (type t x y hyps))
  (met ((hit res) (find-exact-subbagp-instance x hyps))
       (and hit
	    (equal y res))))

(defun bind-subbagp-argument (key xlist x y mfc state)
  (declare (xargs  :guard (and
                           (PSEUDO-TERMP X)
                           (PSEUDO-TERMP y))
                   :stobjs (state)
                   :verify-guards t)
	   (ignore state))
  (if (syntax-subbagp-fn nil x y)
      `((,key   . (quote t))
	(,xlist . (quote nil)))
    (let ((hyps (mfc-clause mfc)))
      (and (not (subbagp-instance x y hyps))
	   (let ((res (find-bounded-subbagp-path t x hyps y hyps (len hyps) nil)))
	     (if (and (consp res)
		      (consp (car res)))
;(prog2$
;(cw "~%dag: bind-subbagp-argument!~%")
		 (let ((type (cdar res)))
		   (let ((path (reverse-path (cdr res) `(quote ,type))))
		     `((,key   . (quote t))
		       (,xlist . ,path))))
	       nil))))))


;add guard?
(defun subbagp-chain (x xlist x0)
  (if (consp xlist)
      (and (if (cdar xlist) (hide-subbagp x (caar xlist)) (meta-subbagp x (caar xlist)))
	   (subbagp-chain (caar xlist) (cdr xlist) x0))
    (if xlist
	(hide-subbagp x x0)
      (meta-subbagp x x0))))

;add guard?
(defun subbagp-hyp (key x xlist y)
  (and key (subbagp-chain x xlist y)))

(defthm subbagp-computation
  (implies (and (bind-free (bind-subbagp-argument 'key 'xlist x y mfc state) (key xlist))
                (subbagp-hyp key x xlist y)
                )
           (subbagp x y))
  :hints (("goal" :in-theory (enable hide-subbagp meta-subbagp))))

(local
 (encapsulate
  ()
  (defthmd tester
    (implies (and (subbagp x y)
                  (subbagp y z)
                  (subbagp z q))
             (subbagp x q)))

  (defthmd tester1
    (implies (and (subbagp x y)
                  (subbagp (append y b) z))
             (subbagp x z)))

  (defthmd tester2
    (implies (subbagp a x)
             (subbagp a (append x y))))

  ))

;-------------------------- UNIQUENESS --------------------------;
;finds a single potential subbagp-path and returns the path
(defun find-subbagp-path (x hyps n res)
  (declare (type (integer 0 *) n)
	   (xargs :guard (and (pseudo-termp x)
                              (pseudo-term-listp hyps))
                  :measure (nfix n)))
  (if (zp n) res
    (met ((hit x0) (find-exact-subbagp-instance x hyps))
	 (if hit
	     (find-subbagp-path x0 hyps (1- n) (cons (cons x0 t) res))
	   (met ((hit x0 x1 rh) (find-syntax-subbagp-instance x hyps))
		(declare (ignore rh))
		(if hit
		    (find-subbagp-path x1 hyps (1- n) (cons (cons x1 t) (cons (cons x0 nil) res)))
		  res))))))

;searches through hyps for a call to UNIQUE which gives us (unique x)
(defun find-unique-instance (x hyps)
  (declare (type t x hyps)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-term-listp hyps))))
  (if (consp hyps)
      (let ((entry (car hyps)))
	(let ((args (and (consp entry)
			 (equal (car entry) 'not)
			 (consp (cdr entry))
			 (let ((fn (cadr entry)))
			   (and (consp fn)
				(equal (car fn) 'unique)
				(consp (cdr fn))
				(cadr fn))))))
	  (if (equal x args)
	      (mv args t)
	    (if (and args (syntax-subbagp-fn nil x args))
		(mv args nil) ;why nil?
	      (find-unique-instance x (cdr hyps))))))
    (mv nil nil)))

;added by eric for guard reasons
(defun list-whose-caars-are-pseudo-termsp (x)
  (declare (type t x))
  (if (consp x)
      (and (consp (car x))
           (pseudo-termp (caar x))
           (list-whose-caars-are-pseudo-termsp (cdr x)))
    t))


(defun find-unique-instance-list (xlist hyps)
  (declare (type t xlist hyps)
           (xargs :guard (and (list-whose-caars-are-pseudo-termsp xlist) ;(pseudo-termp xlist)
                              (pseudo-term-listp hyps))))
  (if (consp xlist)
      (let ((z0 (if (consp (car xlist)) (caar xlist) nil)))
	(met ((uni syntax) (find-unique-instance z0 hyps))
	  (if uni
	      (if syntax
		  xlist
		(append `((,uni . nil) (,z0 . t)) (cdr xlist))) ;reversed since list still needs to be reversed
	    (find-unique-instance-list (cdr xlist) hyps))))
    nil))

(defthm pseudo-termp-of-v2-of-find-syntax-subbagp-instance
  (implies (pseudo-term-listp hyps)
           (pseudo-termp (val 2 (find-syntax-subbagp-instance x hyps)))))

(defthm pseudo-termp-of-v1-of-find-syntax-subbagp-instance
  (implies (pseudo-term-listp hyps)
           (pseudo-termp (val 1 (find-syntax-subbagp-instance x hyps)))))

(defthm pseudo-termp-of-v2-of-find-exact-subbagp-instance
  (implies (pseudo-term-listp hyps)
           (pseudo-termp (val 2 (find-exact-subbagp-instance x hyps)))))

(defthm pseudo-termp-of-v1-of-find-exact-subbagp-instance
  (implies (pseudo-term-listp hyps)
           (pseudo-termp (val 1 (find-exact-subbagp-instance x hyps)))))

(defthm list-whose-caars-are-pseudo-termsp-of-find-subbagp-path
  (implies (and (pseudo-term-listp hyps)
                (list-whose-caars-are-pseudo-termsp res)
                )
           (list-whose-caars-are-pseudo-termsp (find-subbagp-path x hyps n res)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defun unique-uniqueness (x hyps)
  (declare (type t x hyps)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-term-listp hyps))))
  (let ((n (len hyps)))
    (let ((xlist (find-subbagp-path x hyps n `((,x . t)))))
      (let ((newlist (find-unique-instance-list xlist hyps)))
	(let ((uni (if (and (consp newlist) (consp (car newlist))) (caar newlist) nil)))
	  (mv uni (reverse-path newlist '(quote t))))))))

(defun in-hyps-unique (x hyps)
  (declare (type t x hyps))
  (if (consp hyps)
      (let ((entry (car hyps)))
	(if (and (consp entry)
		 (consp (cdr entry)))
	    (if (and (equal (car entry) 'unique)
		     (equal (cadr entry) x))
		t
	      (in-hyps-unique x (cdr hyps)))
	  (in-hyps-unique x (cdr hyps))))
    nil))

(defun bind-unique-argument (key xlist uni x mfc state)
  (declare (xargs :stobjs (state)
                  :guard (pseudo-termp x)
                  )
	   (ignore state))
  (let ((hyps (mfc-clause mfc)))
    (and (or (mfc-ancestors mfc)
	     (in-hyps-unique x hyps))
	 (met ((hit list) (unique-uniqueness x hyps))
		(if hit
		    `((,key . (quote t))
		      (,xlist . ,list)
		      (,uni . ,hit))
		  nil)))))

;; hide-unique is defined in meta as unique

;add guard?
(defun unique-chain (x xlist uni)
  (if (consp xlist)
      (and (if (cdar xlist) (hide-subbagp x (caar xlist)) (meta-subbagp x (caar xlist)));(subbagp x (car xlist))
	   (unique-chain (caar xlist) (cdr xlist) uni))
    (if xlist
	(and (hide-subbagp x uni)
	     (hide-unique uni))
      (and (meta-subbagp x uni)
	   (hide-unique uni)))))

;add guard?
(defun unique-hyp (key x xlist uni)
  (and key (unique-chain x xlist uni)))

(defthm unique-computation
  (implies (and (bind-free (bind-unique-argument 'key 'xlist 'uni x mfc state) (key xlist uni))
                (unique-hyp key x xlist uni))
           (unique x))
  :hints (("Goal" :in-theory (enable hide-unique hide-subbagp meta-subbagp))))

(encapsulate
 ()

 (local
  (defthmd unique-test
    (implies (and (subbagp x y)
                  (subbagp y z)
                  (subbagp z w)
                  (unique w))
             (unique x))))

 (local
  (defthmd unique-test1
    (implies (and (subbagp x y)
                  (subbagp (append y p) z)
                  (subbagp z w)
                  (unique w))
             (unique x))))

 (local
  (defthmd unique-test2
    (implies (unique (append x y))
             (unique x))))

 (local
  (defthmd unique-test3
    (implies (and (subbagp x a)
                  (unique (append a y)))
             (unique x))))

 (local
  (defthmd unique-test4
    (implies (and (subbagp x a)
                  (subbagp a y)
                  (subbagp y z)
                  (unique y))
             (unique x))))

 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;--------------------------DISJOINTNESS---------------------------
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-disjointness (x y hyps)
  (declare (type t x y hyps)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (pseudo-term-listp hyps)
                              )
                  ))
  (if (consp hyps)
      (let ((entry (car hyps)))
	(let ((args (and (consp entry)
			 (equal (car entry) 'not)
			 (consp (cdr entry))
			 (let ((fn (cadr entry)))
			   (and (consp fn)
				(equal (car fn) 'disjoint)
				(consp (cdr fn))
				(consp (cddr fn))
				(cons (cadr fn) (caddr fn)))))))
	  (if (equal args nil)
	      (find-disjointness x y (cdr hyps))
	    (if (syntax-subbagp-pair-fn nil x y (car args) (cdr args))
		(mv t t (car args) (cdr args))
	      (if (syntax-subbagp-pair-fn nil x y (car args) (cdr args))
		  (mv t nil (car args) (cdr args))
		(find-disjointness x y (cdr hyps)))))))
    (mv nil nil nil nil))) ;return list is hit syntax p q

(defun find-disjointness* (x ylist hyps)
  (declare (type t x ylist hyps)
           (xargs :guard (and (pseudo-termp x)
                              (list-whose-caars-are-pseudo-termsp ylist)
                              (pseudo-term-listp hyps))
                  ))

  (if (and (consp ylist)
	   (consp (car ylist)))
      (met ((hit syn p q) (find-disjointness  x (caar ylist) hyps))
	   (if hit
	       (mv hit syn p q ylist)
	     (find-disjointness* x (cdr ylist) hyps)))
    (mv nil nil nil nil nil)))

(defun find-disjointness** (xlist ylist hyps)
  (declare (type t xlist ylist hyps)
           (xargs :guard (and (list-whose-caars-are-pseudo-termsp xlist)
                              (list-whose-caars-are-pseudo-termsp ylist)
                              (pseudo-term-listp hyps))
                             ))
  (if (and (consp xlist)
	   (consp (car xlist)))
      (met ((hit syn p q ylist2) (find-disjointness*  (caar xlist) ylist hyps))
	   (if hit
	       (mv hit syn xlist ylist2 p q)
	     (find-disjointness** (cdr xlist) ylist hyps)))
    (mv nil nil nil nil nil nil)))

;checks for subbagp paths up to disjoint
;argument for disjointness comes from a disjoint in hyps
(defun disjoint-disjointness (x y hyps)
  (declare (type t x hyps)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (pseudo-term-listp hyps))
                  ))
  (let ((n (len hyps)))
    (let ((xlist (find-subbagp-path x hyps n `((,x . t))))
	  (ylist (find-subbagp-path y hyps n `((,y . t)))))
      (met ((hit syn newx newy p q) (find-disjointness** xlist ylist hyps))
	   (if hit
	       (let ((x0 (if (and (consp newx) (consp (car newx))) (caar newx) nil))
		     (y0 (if (and (consp newy) (consp (car newy))) (caar newy) nil)))
		 (mv t ;key
		     (reverse-path newx '(quote t)) ;xlist
		     x0
		     (reverse-path newy '(quote t)) ;ylist
		     y0
		     `(quote ,syn)
		     p
		     q)) ;z's are irrelevent in this argument
;but use z positions for subbagp-pair type argument
	     (mv nil nil nil nil nil nil nil nil) ;no disjoint hyp found
	     )))))
;move?
(defun revlist (list res)
  (declare (type t list res))
  (if (consp list)
      (revlist (cdr list) (cons (car list) res))
    res))

(defun find-subbagp-pair-zlist (x y zlist)
  (declare (type t x y zlist)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (list-whose-caars-are-pseudo-termsp zlist))
                  ))
  (if (consp zlist)
      (let ((args (and (consp (car zlist))
		       (caar zlist))))
	(if (syntax-unique-subbagps-fn nil x y args) ;once you have this, want to return list from args to unique
	    (let ((newzlist (revlist zlist nil)))
	      (let ((z0 (if (and (consp newzlist) (consp (car newzlist))) (caar newzlist) nil)))
		(mv t args newzlist z0)))
	  (find-subbagp-pair-zlist x y (cdr zlist))))
    (mv nil nil nil nil)))


(defthm LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP-of-revlist
  (IMPLIES (AND (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP list)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP res))
           (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP (REVLIST list res))))


(defun find-unique-subbagp (x y zlist hyps)
  (declare (type t x y hyps zlist)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (pseudo-term-listp hyps)
                              (list-whose-caars-are-pseudo-termsp zlist))
                  ))
  (if (consp hyps)
      (let ((entry (car hyps)))
	(let ((args (and (consp entry)
			 (equal (car entry) 'not)
			 (consp (cdr entry))
			 (let ((fn (cadr entry)))
			   (and (consp fn)
				(equal (car fn) 'unique)
				(consp (cdr fn))
				(cadr fn))))))
	  (if (and args (syntax-unique-subbagps-fn nil x y args)) ;if subbagp-pair of something unique
	      (mv t args nil nil) ;(hit unique-element not-chain)
	    (find-unique-subbagp x y zlist (cdr hyps)))))
    (met ((hit first chain z0) (find-subbagp-pair-zlist x y (revlist zlist nil)))
	 (mv hit first (reverse-path chain '(quote t)) z0))))

(defun find-unique-subbagp* (x ylist zlist hyps)
  (declare (type t x ylist zlist hyps)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-term-listp hyps)
                              (list-whose-caars-are-pseudo-termsp ylist)
                              (list-whose-caars-are-pseudo-termsp zlist))
                  ))
  (if (and (consp ylist)
	   (consp (car ylist)))
      (met ((hit z chain z0) (find-unique-subbagp x (caar ylist) zlist hyps))
	   (if hit
	       (mv t (caar ylist) ylist z chain z0)
	     (find-unique-subbagp* x (cdr ylist) zlist hyps)))
    (mv nil nil nil nil nil nil)))

(defun find-unique-subbagp** (xlist ylist zlist hyps)
  (declare (type t xlist ylist zlist hyps)
           (xargs :guard (and (pseudo-term-listp hyps)
                              (list-whose-caars-are-pseudo-termsp ylist)
                              (list-whose-caars-are-pseudo-termsp xlist)
                              (list-whose-caars-are-pseudo-termsp zlist))
                  ))
  (if (and (consp xlist)
	   (consp (car xlist)))
      (met ((hit y0 ylist z chain z0) (find-unique-subbagp* (caar xlist) ylist zlist hyps))
	   (if hit
	       (if (not chain)
		   (mv t xlist (caar xlist) ylist y0 z '(quote nil) z)
		 (mv t xlist (caar xlist) ylist y0 z chain z0))
	     (find-unique-subbagp** (cdr  xlist) ylist zlist hyps)))
    (mv nil nil nil nil nil nil nil nil)))

(defun find-shared-ancestor-list (x ylist yres)
  (declare (type t x ylist yres))
  (if (consp ylist)
      (if (and (consp (car ylist))
	       (equal x (caar ylist)))
	  (mv t yres)
	(find-shared-ancestor-list x (cdr ylist) (cons (car ylist) yres)))
    (mv nil nil)))

(defun find-shared-ancestor (xlist ylist xres)
  (declare (type t xlist ylist xres))
  (if (and (consp xlist)
	   (consp (car xlist)))
      (met ((hit yres) (find-shared-ancestor-list (caar xlist) ylist nil))
	   (if hit (mv xres yres xlist)
	     (find-shared-ancestor (cdr xlist) ylist (cons (car xlist) xres))))
    (mv xres (revlist ylist nil) nil)))


(defthm LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP-of-v0-of-FIND-SHARED-ANCESTOR
  (implies (and (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xlist)
               ; (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP ylist)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xres)
                )
           (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP
            (VAL
             0
             (FIND-SHARED-ANCESTOR XLIST YLIST XRES)))))

(defthm LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP-of-v1-of-FIND-SHARED-ANCESTOR-list
  (implies (and; (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xlist)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP ylist)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP yres)
                )
           (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP
            (VAL
             1
             (FIND-SHARED-ANCESTOR-list X YLIST yRES)))))

(defthm LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP-of-v1-of-FIND-SHARED-ANCESTOR
  (implies (and (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xlist)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP ylist)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xres)
                )
           (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP
            (VAL
             1
             (FIND-SHARED-ANCESTOR XLIST YLIST XRES)))))

(defthm LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP-of-v2-of-FIND-SHARED-ANCESTOR
  (implies (and (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xlist)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP ylist)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xres)
                )
           (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP
            (VAL
             2
             (FIND-SHARED-ANCESTOR XLIST YLIST XRES)))))

(defthm PSEUDO-TERMP-of-v0-of-FIND-UNIQUE-INSTANCE
  (implies (PSEUDO-TERM-LISTP HYPS)
           (PSEUDO-TERMP (VAL 0 (FIND-UNIQUE-INSTANCE x HYPS)))))

(defthm LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP-of-FIND-UNIQUE-INSTANCE-LIST
  (IMPLIES (AND (PSEUDO-TERM-LISTP HYPS)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xlist)
                )
           (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP (FIND-UNIQUE-INSTANCE-LIST xlist hyps))))

(defun unique-disjointness (x y hyps)
  (declare (type t x y hyps)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (pseudo-term-listp hyps))
                  ))

  (let ((n (len hyps)))
    (let ((xlist (find-subbagp-path x hyps n `((,x . t))))
	  (ylist (find-subbagp-path y hyps n `((,y . t)))))
      (let ((xlist (revlist xlist nil))
	    (ylist (revlist ylist nil)))               ; smallest to largest
	(met ((xlist ylist zlist) (find-shared-ancestor xlist ylist nil)) ; x/y largest to smallest

	     (let ((newzlist (find-unique-instance-list (revlist zlist nil) hyps)))
	       ;; newzlist path from something unique down subbagps
	       (met ((hit newxlist x0 newylist y0 z zlist z0) (find-unique-subbagp** xlist ylist newzlist hyps))
		    (mv hit (reverse-path newxlist '(quote t))
			x0  (reverse-path newylist '(quote t))
			y0 z zlist z0))))))))

;search for (disjoint X Y) in CLAUSE
;since we look for it non-negated, we are essentially looking for it as a conclusion
(defun in-clause-disjoint (x y clause)
  (declare (type t x y clause))
  (if (consp clause)
      (let ((entry (car clause)))
	(if (and (consp entry)
		 (equal (car entry) 'disjoint)
                 (consp (cdr entry))
		 (equal (cadr entry) x)
                 (consp (cddr entry))
                 (equal (caddr entry) y))
	    t
	  (in-clause-disjoint x y (cdr clause))))
    nil))

(defun bind-disjoint-argument (flg key xlist x0 ylist y0 z zlist z0 x y mfc state)
  (declare (xargs :stobjs (state)
                  :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              )
                  )
	   (ignore state))
  (let ((hyps (mfc-clause mfc)))
    (and (or flg
	     t
             (mfc-ancestors mfc) ;BOZO why are we doing these checks?
	     (in-clause-disjoint x y hyps)
             )
	 (met ((hit xlist* x0* ylist* y0* z* zlist* z0*) (unique-disjointness x y hyps))
	      (if hit
		  `((,key . (quote :unique))
		    (,xlist . ,xlist*)
		    (,x0 . ,x0*)
		    (,ylist . ,ylist*)
		    (,y0 . ,y0*)
		    (,z . ,z*)
		    (,zlist . ,zlist*)
		    (,z0 . ,z0*))
		(met ((hit xlist* x0* ylist* y0* z* zlist* z0*) (disjoint-disjointness x y hyps))
		     (if hit
			 `((,key . (quote :disjoint))
			   (,xlist . ,xlist*)
			   (,x0 . ,x0*)
			   (,ylist . ,ylist*)
			   (,y0 . ,y0*)
			   (,z . ,z*)
			   (,zlist . ,zlist*)
			   (,z0 . ,z0*))
		       nil)))))))

;rename!
(defthm subbagp-pair-x-x-y-y
  (subbagp-pair x y x y)
  :hints (("goal" :in-theory (enable subbagp-pair))))

;add guard?
(defun unique-subbagp-chain (x0 y0 z zlist z0)
  (and (unique-subbagps x0 y0 z)
       (unique-chain z zlist z0)))

;add guard?
(defun disjoint-hyp (key x xlist x0 y ylist y0 z-syn zlist-p z0-q)
  (cond
   ((equal key ':disjoint)
    (and (subbagp-pair x0 y0 zlist-p z0-q)
	 (hide-disjoint zlist-p z0-q)
	 (subbagp-chain x xlist x0)
	 (subbagp-chain y ylist y0)))
   ((equal key ':unique)
    (and
     (unique-subbagp-chain x0 y0 z-syn zlist-p z0-q)
     (subbagp-chain x xlist x0)
     (subbagp-chain y ylist y0)
     ))
   (t nil)))


(encapsulate
 ()
 (local ;theorems to prove disjoint-computation
  (encapsulate
   ()
   (defthm subbagp-chain-subbagp
     (implies (subbagp-chain x xlist x0)
              (subbagp x x0))
     :hints (("goal" :in-theory (enable hide-subbagp meta-subbagp))))

   (defthm subbagp-subbagp-pair-disjoint
     (implies (and (subbagp-pair x0 y0 z z0)
                   (disjoint z z0))
              (disjoint x0 y0))
     :hints (("goal" :in-theory (enable subbagp-pair))))

   (defthm subbagp-subbagp-disjoint-disjoint
     (implies (and (subbagp x x0)
                   (subbagp y y0)
                   (disjoint x0 y0))
              (disjoint x y)))

   (defthm pair-chain-disjoint
     (implies (and (subbagp-pair x0 y0 zlist z0)
                   (disjoint z0 zlist)
                   (subbagp x x0)
                   (subbagp-chain y ylist y0))
              (disjoint x y))
     :hints (("Goal" :in-theory (enable hide-disjoint meta-subbagp hide-subbagp hide-unique))))

   (defthm unique-chain-unique
     (implies (unique-chain x xlist x0)
              (unique x))
     :hints (("Goal" :in-theory (enable meta-subbagp hide-unique hide-subbagp))))

   (defthm unique-subbagp-chain-unique
     (implies (and (subbagp x y)
                   (unique-chain y z w))
              (unique x))
     :hints (("Goal" :in-theory (enable meta-subbagp hide-unique hide-subbagp))))

   (defthm subbagp-unique-subbagps-chains
     (implies (and (unique z0)
                   (subbagp z z0)
                   (unique-subbagps x0 y0 z)
                   (subbagp-chain x xlist x0)
                   (subbagp-chain y ylist y0))
              (disjoint x y))
     :hints (("Goal" :use ((:instance
                            *trigger*-unique-subbagps-implies-disjointness
                            (list z) (x x0) (y y0))))))

   )) ;close the local


 (defthmd disjoint-computation-lemma ;trying disabled.  make local?
   (implies (disjoint-hyp key x xlist x0 y ylist y0 z zlist z0)
            (disjoint x y))
   :hints (("Goal" :in-theory (enable hide-disjoint meta-subbagp hide-subbagp hide-unique))
           ("Subgoal *1/1''" :use ((:instance
                                    *trigger*-unique-subbagps-implies-disjointness
                                    (list z) (x x0) (y y0)))))
   :rule-classes :forward-chaining)

 (defthm disjoint-computation
   (implies (and (bind-free (bind-disjoint-argument nil 'key 'xlist 'x0 'ylist 'y0 'z 'zlist 'z0 x y mfc state)
                            (key xlist x0 ylist y0 z zlist z0))
                 (disjoint-hyp key x xlist x0 y ylist y0 z zlist z0))
            (disjoint x y))
   :hints (("Goal" :in-theory (enable  disjoint-computation-lemma)))
   )
 ) ;close the encapsulate

 ;tests for disjoint computation
(encapsulate
 ()

 (local
  (in-theory (disable subbagp-disjoint unique-of-append)))

 (local
  (defthmd disjoint-test
    (implies (and (subbagp x (append x0 x1))
                  (subbagp (append x0 x1) x2)
                  (subbagp y y1)
                  (subbagp y1 y2)
                  (disjoint x2 y2))
;(disjoint x1 y1))
             (disjoint x y))))

 (local
  (defthmd disjoint-test1
    (implies (and (subbagp x x1)
                  (subbagp x1 (append x2 x3))
                  (subbagp y y1)
                  (subbagp y1 y2)
                  (disjoint x1 y2))
             (disjoint x y))))

 (local
  (defthmd disjoint-test2
    (implies (and (subbagp x x0)
                  (subbagp y y0)
                  (unique (append x0 y0)))
             (disjoint x y))))

 (local
  (defthmd disjoint-test3
    (implies (and (subbagp x (append x1 x2))
                  (subbagp (append x1 x2) x3)
                  (subbagp y y1)
                  (disjoint y1 x3))
             (disjoint x y))))

 (local
  (defthmd disjoint-test4
    (implies (and (subbagp x x0)
                  (subbagp y y0)
                  (subbagp (append x0 y0) z)
                  (subbagp z z0)
                  (subbagp z0 z1)
                  (unique z1)
                  ;(unique z0)
                  )
             (disjoint x y))))

 (local
  (defthmd disjoint-test5
    (implies (and (subbagp y v)
                  (subbagp w u)
                  (memberp x w)
                  (disjoint u v)
                  (memberp x y)
                  )
             (disjoint w y))))
 ) ;encapsulate

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;----------------------------- MEMBERP --------------------------------
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Collect up a list of all BLAH such that (memberp X BLAH) exists as a hyp in CLAUSE
(defun find-memberp-instance-list (x clause res)
  (declare (type t x clause res))
  (if (consp clause)
      (let ((entry (car clause)))
	(if (and (consp entry)
		; (not (memberp x x0))
		 (equal (car entry) 'not)
		 (consp (cdr entry))
		 (consp (cadr entry))
		 (equal (car (cadr entry)) 'memberp)
		 (consp (cdr (cadr entry)))
		 (consp (cddr (cadr entry)))
		 (equal (cadr (cadr entry)) x))
	    (find-memberp-instance-list x (cdr clause)
				       (cons (caddr (car (cdr entry))) res))
	  (find-memberp-instance-list x (cdr clause) res)))
    res))

(defun find-memberp-subbagp-list (x0list y hyps)
  (declare (type t x0list y hyps)
           (xargs :guard (and (pseudo-termp y)
                              (pseudo-term-listp hyps)
                              (pseudo-term-listp x0list))
                  )
           )
  (if (consp x0list)
      (let ((x0 (car x0list)))
	(let ((res (find-bounded-subbagp-path t x0 hyps y hyps (len hyps) nil)))
          (if (and (consp res)
                   (consp (car res)))
              (let ((type (cdar res)))
                (let ((path (reverse-path (cdr res) `(quote ,type))))
                  (mv t x0 path)))
            (find-memberp-subbagp-list (cdr x0list) y hyps))))
    (mv nil nil nil)))

(defthm PSEUDO-TERM-LISTP-of-FIND-MEMBERP-INSTANCE-LIST
  (IMPLIES (AND (PSEUDO-TERM-LISTP clause)
                (PSEUDO-TERM-LISTP res)
                )
           (PSEUDO-TERM-LISTP (FIND-MEMBERP-INSTANCE-LIST x clause res))))

(defun memberp-membership (x y hyps)
  (declare (type t x y hyps)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (pseudo-term-listp hyps))
                  ))
  (let ((x0list (find-memberp-instance-list x hyps nil)))
    (met ((hit x0 path) (find-memberp-subbagp-list x0list y hyps))
	 (mv hit x0 path))))

(defun in-hyps-memberp (x y hyps)
  (declare (type t x y hyps))
  (if (consp hyps)
      (let ((entry (car hyps)))
	(if (and (consp entry)
		 (consp (cdr entry))
		 (consp (cddr entry)))
	    (if (and (equal (car entry) 'memberp)
		     (equal (cadr entry) x)
		     (equal (caddr entry) y))
		t
	      (in-hyps-memberp x y (cdr hyps)))
	  (in-hyps-memberp x y (cdr hyps))))
    nil))

(defun bind-memberp-argument (key xlist x0 x y mfc state)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              )
                  :stobjs (state)
                  )
	   (ignore state))
  (let ((hyps (mfc-clause mfc)))
    (and (or (mfc-ancestors mfc)
	     (in-hyps-memberp x y hyps))
	 (met ((hit val list) (memberp-membership x y hyps))
	      (if hit
		  `((,key . (quote t))
		    (,x0 . ,val)
		    (,xlist . ,list))
		nil)))))


;add guard?
(defun memberp-hyp (key x x0 xlist y)
  (and key
       (hide-memberp x x0)
       (subbagp-chain x0 xlist y)))

(defthm memberp-computation
  (implies
   (and
    (bind-free (bind-memberp-argument 'key 'xlist 'x0 x y mfc state)
	       (key x0 xlist))
    (memberp-hyp key x x0 xlist y)
    )
   (memberp x y))
  :hints (("goal" :in-theory (enable hide-subbagp meta-subbagp hide-memberp))))

(local (in-theory (disable memberp-of-append)))

(encapsulate
 ()

 (local
  (defthmd memberp-test
    (implies (and (memberp x z)
                  (subbagp z w)
                  (subbagp w y)
                  (subbagp y u))
             (memberp x (append u v)))))

 (local
  (defthmd memberp-test1
    (implies (and (memberp x z)
                  (subbagp z w)
                  (subbagp w y))
             (memberp x y))))



 (local
  (defthmd memberp-test2
    (implies (and (memberp x (append u v))
                  (subbagp (append u v) w)
                  (subbagp w y))
             (memberp x y))))

 )


;------------------------ NON-MEMBERP -------------------------;
(defun remove-y (list y res)
  (declare (type t list y res))
  (if (consp list)
      (if (equal (car list) y)
	  (cdr list)
	(remove-y (cdr list) y (cons (car list) res)))
    res))

(defun in-hyps-not-memberp (x y hyps)
  (declare (type t x y hyps))
  (if (consp hyps)
      (let ((entry (car hyps)))
	(if (and (consp entry)
		 (equal (car entry) 'not)
		 (consp (cdr entry))
		 (let ((fn (cadr entry)))
		   (and (consp fn)
			(consp (cdr fn))
			(consp (cddr fn))
			(equal (car fn) 'memberp)
			(equal (cadr fn) x)
			(equal (caddr fn) y))))
	    t
	  (in-hyps-not-memberp x y (cdr hyps))))
    nil))

(defun disjoint-not-membership (memlist y mfc state)
  (declare (xargs :stobjs (state)
                  :guard (and (pseudo-termp y)
                              (pseudo-term-listp memlist)
                              )
                  ))
  (if (consp memlist)
      (let ((x* (car memlist)))
	(let ((disjoint-arg
	       (bind-disjoint-argument t 'key 'xlist 'x0 'ylist 'y0 'z 'zlist 'z0 x* y mfc state)))
	  (if disjoint-arg
	      (mv t x* disjoint-arg)
	    (disjoint-not-membership (cdr memlist) y mfc state))))
    (mv nil nil nil)))

(defthm PSEUDO-TERM-LISTP-of-REMOVE-Y
  (IMPLIES (and (PSEUDO-TERM-LISTP list)
                (PSEUDO-TERM-LISTP res))
           (PSEUDO-TERM-LISTP (REMOVE-Y list y res))))

(defun bind-non-memberp-argument (hit x* x y mfc state)
  (declare (xargs :stobjs (state)
                  :guard (and (pseudo-termp x)
                              (pseudo-termp y)
;                              (pseudo-term-listp memlist)
                              )
                  )
;(ignore state)
	   )
  (let ((hyps (mfc-clause mfc)))
    (and (or (mfc-ancestors mfc)
	     (in-hyps-not-memberp x y hyps))
	 (let ((memlist (remove-y (find-memberp-instance-list x hyps nil) y nil)))
	   (met ((hit1 x*1 disjoint-arg) (disjoint-not-membership memlist y mfc state))
		(if (and hit1 (alistp disjoint-arg))
		    (append `((,hit . (quote t))
			      (,x* . ,x*1))
			    disjoint-arg)
		  nil))))))

;add guard?
(defun non-memberp-hyp (hit x* key x xlist x0 y ylist y0 z zlist z0)
  (and hit
       (hide-memberp x x*)
       (disjoint-hyp key x* xlist x0 y ylist y0 z zlist z0)))

(defthm non-memberp-computation
  (implies
   (and
    (bind-free (bind-non-memberp-argument 'hit 'x* x y mfc state)
	       (hit x* key xlist x0 ylist y0 z zlist z0))
    (non-memberp-hyp hit x* key x xlist x0 y ylist y0 z zlist z0))
   (not (memberp x y)))
  :hints (("goal" :in-theory (e/d (hide-memberp disjoint-computation-lemma) (disjoint-hyp)))))

(encapsulate
 ()

 (local
  (defthmd non-memberp-test
    (implies (and (subbagp y v)
                  (subbagp w u)
                  (memberp x w)
                  (disjoint u v))
             (not (memberp x y)))))

 (local
  (defthmd non-memberp-test1
    (implies (and (not (disjoint q w))
                  (not (subbagp g h))
                  (subbagp p q)
                  (subbagp q (append r s))
                  (subbagp (append r s) v)
                  (memberp a j)
                  (subbagp j (append k l))
                  (subbagp (append k l) m)
                  (disjoint m v)
                  (disjoint i o)
                  )
             (not (memberp a p)))))
 )




(in-theory (disable
            memberp ;just in case
            disjoint
;                           MEMBERP-SUBBAGP-NOT-CONSP-VERSION
            REMOVE-BAG
            REMOVE-1))

;;; from proof-common.lisp:


(defun find-remove-bag-instance-unique (y z term)
  (declare (type t term))
  (and (consp term)
       (if (and (equal (car term) 'binary-append) ; (binary-append a b)
		(consp (cdr term))
		(consp (cddr term)))
	   (or (let ((a (cadr term)))
		 (and (consp a)
		      (equal (car a) 'remove-bag) ; (remove-bag x y)
		      (consp (cdr a))
		      (consp (cddr a))
		      (let ((zed nil)) ; (cw "x = ~p0 ~%" (caddr a))))
			(declare (ignore zed))
			(or (and (equal y (caddr a))
				 (cons t (cadr a)))
			    (and (equal z (caddr a))
				 (cons nil (cadr a)))))))
	       (find-remove-bag-instance-unique y z (caddr term)))
	 (and (equal (car term) 'remove-bag)
	      (and (consp (cdr term))
		   (consp (cddr term))
		   (or (and (equal y (caddr term))
			    (cons t (cadr term)))
		       (and (equal z (caddr term))
			    (cons nil (cadr term)))))))))

;walk through hyps until we find (unique BLAH), then try to show ... what exactly??
(defun find-remove-bag-instance-hyps (y z hyps)
  (declare (type t hyps))
  (and (consp hyps)
       (or (let ((hyp (car hyps)))
	     (and (consp hyp)  ; (not (unique ..))
		  (equal (car hyp) 'not)
		  (consp (cdr hyp))
		  (let ((term (cadr hyp))) ; (unqiue list)
		    (and (consp term)
			 (equal (car term) 'unique)
			 (consp (cdr term))
			 (find-remove-bag-instance-unique y z (cadr term))))))
	   (find-remove-bag-instance-hyps y z (cdr hyps)))))

(defun bind-remove-bag-instance-fn (y z which val mfc state)
  (declare (xargs :stobjs (state)
		  :verify-guards t)
	   (ignore state))
  (let ((hyps (mfc-clause mfc)))
    (let ((zed nil)); (cw "y = ~p0 ~%" y)))
      (declare (ignore zed))
      (let ((zed nil)); (cw "z = ~p0 ~%" z)))
	(declare (ignore zed))
	(let ((x (find-remove-bag-instance-hyps y z hyps)))
	  (and x
	       `((,which . (quote ,(car x)))
		 (,val   . ,(cdr x)))))))))

(defmacro bind-remove-bag-instance (y z which val)
  `(bind-free (bind-remove-bag-instance-fn ,y ,z (quote ,which) (quote ,val) mfc state)
	      (,which ,val)))

;add guard?
(defun disjoint-other-hyp (which x y z)
  (if which
      (disjoint (append x (remove-bag x y))
                z)
    (disjoint (append x (remove-bag x z)) y)))

(defthm disjoint-other-memberp
  (implies (and (bind-remove-bag-instance y z which x)
                (disjoint-other-hyp which x y z))
           (disjoint y z)))

;add guard?
(defun collect-list (term)
  (if (and (consp term)
	   (equal (car term) 'remove-1))
      `(cons ,(cadr term)
	     ,(collect-list (caddr term)))
    `(quote nil)))

;add guard?
(defun collect-rest (term)
  (if (and (consp term)
	   (equal (car term) 'remove-1))
      (collect-rest (caddr term))
    term))

;add guard?
(defun bind-list (list rest term)
  `((,list . ,(collect-list term))
    (,rest . ,(collect-rest term))))

;this could be expensive?  could we just change syntax-subbagp to consider
;(remove-1 a y) to be a subset of x whenever y is a subset of x?

(defthm bind-subbagp-remove-bag
  (implies (and (subbagp x term)
                (bind-free (bind-list 'list 'rest term) (list rest))
                (equal y rest)
                (equal term (remove-bag list rest)))
           (subbagp x y))
  :hints (("goal" :in-theory (enable subbagp-remove-bag))))

(defthm bind-memberp-remove-bag
  (implies (and (memberp sblk term)
                (bind-free (bind-list 'list 'rest term) (list rest))
                (equal y rest)
                (equal term (remove-bag list rest)))
           (memberp sblk y)))
