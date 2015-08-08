(in-package "ACL2")

#|

  stutter2.lisp
  ~~~~~~~~~~~~~

In this book, we prove that the stuttering of the bakery
implementation is finite. In particular, a function rank, that is
shown to be a msrp decreases in that case, under the assumption of
fair selection. The theorems we prove are

(DEFTHM well-founded->>
  (msrp (rank st)))

(DEFTHM >>-stutter2
  (implies (and (fair-suff st X)
		(not (commit st (fair-select (env st) X))))
	   (msr< (rank (fair-bake+ st X))
		       (rank st))))

|#

(include-book "programs")
(include-book "properties")
(include-book "lexicographic-pos")

;; [Jared] switched to arithmetic-3 instead of 2
(local (include-book "arithmetic-3/bind-free/top" :dir :system))

(defun rank-proc (i p)
  (if (equal (loc p) i) 1 0))

(defun rank-keys (i procs keys)
  (if (endp keys) 0
    (+ (rank-proc i (<- procs (first keys)))
       (rank-keys i procs (rest keys)))))

(defun locs-for-not-queue ()
  (list 0 2 4))

(defun sequence-measure (procs keys locs)
  (if (endp locs) nil
    (cons (rank-keys (first locs) procs keys)
          (sequence-measure procs keys (rest locs)))))

(defun unfair-measure (procs in)
  (let ((p (<- procs in)))
    (case (loc p)
      ((0 1 2 3 4 5) (list (- 12 (loc p)) 0 5))
      ((6 7 8 9) (list 5 (len (indices p)) (- 12 (loc p))))
      (t (list 7 0 5)))))

(defun rank-procs (procs keys queue env locs)
  (let* ((current (current (<- procs (first queue))))
	 (curr-p (<- procs current)))
    (append (sequence-measure procs keys locs)
            (unfair-measure procs (first queue))
	    (unfair-measure procs (current (<- procs (first queue))))
            (if (or (and (choosing curr-p)
			 (equal (loc (<- procs (first
						queue))) 7))
                    (and (pos curr-p)
			 (pos (<- procs (first queue)))
			 (lex< (pos curr-p)
                               current
                               (pos (<- procs (first queue)))
                               (first queue))
                         (equal (loc (<- procs (first queue))) 8)))
		(fair-measure env current)
	      (btm-measure))
            (fair-measure env (first queue)))))

(defun rank-b-c (st)
  (let* ((procs (procs st))
         (keys (keys (procs st)))
         (queue (queue st))
         (env (env st))
         (locs (locs-for-not-queue)))
  (rank-procs procs keys queue env locs)))

;; END definition of rank function

(DEFTHM well-founded-b-c->>
  (msrp (rank-b-c st))
  :rule-classes nil)

(local
(defthm normalize-append
  (equal (append a (append b c) d)
         (append a b c d)))
)

;; We break the >>-stutter2 theorem up into a number of cases. I have toiled
;; with ACL2 long enough hoping I would make the case split automatic, but I
;; simply could not do it.


;; Case 1: (not (memberp in queue))

(local
(defthm not-consp-queue-implies-loc=0-1-2
  (implies (and (suff-proc procs in bucket queue max)
                (not (commit-proc (<- procs in)))
                (not (memberp in queue)))
           (or (equal (loc (<- procs in)) 0)
               (equal (loc (<- procs in)) 2)))
  :rule-classes :forward-chaining)
)

(local
(defthm memberp-expands-for-constant-list
  (implies (and (syntaxp (quotep locs))
                (true-listp locs))
           (equal (memberp in locs)
                  (if (null locs) nil
                    (implies (not (equal in (first locs)))
                             (memberp in (rest locs)))))))
)

(local
(in-theory (enable bake+-p))
)

(local
(defthm rank-keys-if-something-else-set
  (implies (and (not (equal (loc p) i))
                (not (equal (loc (<- procs in)) i)))
           (equal (rank-keys i (-> procs in p) keys)
                  (rank-keys i procs keys)))
  :hints (("Subgoal *1/2"
           :cases ((equal in (car keys))))))
)

(local
(defthm rank-keys-is-same-for-every-process-before
  (implies (and (memberp (loc (<- procs in)) (locs-for-not-queue))
                (memberp a (locs-for-not-queue))
                (< a (loc (<- procs in))))
           (equal (rank-keys a
                             (-> procs in
                                 (bake+-p (<- procs in) in procs max))
                             keys)
                  (rank-keys a procs keys))))
)

(local
(defthm rank-keys-is->0
  (implies (memberp in keys)
           (> (rank-keys (loc (<- procs in)) procs keys) 0)))
)
(local
 (defthm rank-keys-decreases-if-moved
   (implies (and (memberp in keys)
                 (not (equal (loc p) a))
                 (equal (loc (<- procs in)) a))
            (< (rank-keys a (-> procs in p) keys)
               (rank-keys a procs keys)))
   ;; [Jared] avoid explicit subgoal for switch to arithmetic-3.
   :hints((and stable-under-simplificationp
               '(:cases ((equal in (car keys)))))))
)

(local
(defthm sequence-measure-decreases-1
  (implies (and (memberp in keys)
                (equal (loc (<- procs in)) 0))
           (msr< (sequence-measure (-> procs in (bake+-p (<- procs in) in procs
                                                         max))
                                   keys
                                   (locs-for-not-queue))
                 (sequence-measure procs keys (locs-for-not-queue)))))
)

(local
(defthm sequence-measure-decreases-2
  (implies (and (memberp in keys)
                (equal (loc (<- procs in)) 2))
           (msr< (sequence-measure (-> procs in (bake+-p (<- procs in) in procs
                                                         max))
                                   keys
                                   (locs-for-not-queue))
                 (sequence-measure procs keys (locs-for-not-queue)))))
)

(local
(defthm sequence-measure-decreases-3
  (implies (and (memberp in keys)
                (equal (loc (<- procs in)) 4))
           (msr< (sequence-measure (-> procs in (bake+-p (<- procs in) in procs
                                                         max))
                                   keys
                                   (locs-for-not-queue))
                 (sequence-measure procs keys (locs-for-not-queue)))))
)

(local
(defthm unfair-measure-has-len-3
  (equal (len (unfair-measure procs in))
         3))
)

(local
(defthm unfair-measure-is-nat-listp
  (nat-listp (unfair-measure procs in)))
)

(local
(defthm top-and-bottom-have-same-len
  (equal (len (top-measure))
         (len (btm-measure)))
  :hints (("Goal"
           :in-theory (disable top-measure-is-len=0-fair-measure
                               btm-measure-is-len=0-fair-measure)
           :use (top-measure-is-len=0-fair-measure
                 btm-measure-is-len=0-fair-measure))))
)

(local
(defthm rank-decreases-if-not-member-queue
  (implies (and (memberp in keys)
                (suff-proc procs in bucket queue max)
                (not (commit-proc (<- procs in)))
                (not (memberp in queue)))
            (msr< (rank-procs (-> procs in (bake+-p (<- procs in) in
						    procs max))
                             keys queue (fair-step env X)
			     (locs-for-not-queue))
                 (rank-procs procs keys queue env (locs-for-not-queue))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable bake+-p locs-for-not-queue unfair-measure
                               suff-proc commit-proc
                               (:executable-counterpart locs-for-not-queue))
           :cases ((equal (loc (<- procs in)) 0)
                   (equal (loc (<- procs in)) 2)))))
)

;; END case 1: (not (memberp in queue))

;; case 2: (and (memberp in queue)
;;              (memberp in (locs-for-not-queue)))

(local
(defthm memberp-of-locs-and-queue-implies-loc=2
  (implies (and (suff-proc procs in bucket queue max)
                (not (commit-proc (<- procs in)))
                (memberp (loc (<- procs in)) (locs-for-not-queue))
                (memberp in queue))
           (or (equal (loc (<- procs in)) 2)
               (equal (loc (<- procs in)) 4)))
  :rule-classes :forward-chaining)
)

(local
(defthm rank-keys-decreases-if-member-of-locs
  (implies (and (suff-proc procs in bucket queue max)
                (not (commit-proc (<- procs in)))
                (memberp in keys)
                (memberp (loc (<- procs in)) (locs-for-not-queue))
                (memberp in queue))
           (msr< (rank-procs (-> procs in (bake+-p (<- procs in) in procs max))
                             keys queue (fair-step env X)
			     (locs-for-not-queue))
                 (rank-procs procs keys queue env (locs-for-not-queue))))
  :hints (("Goal"
	   :do-not-induct t
           :cases ((equal (loc (<- procs in)) 2)
                   (equal (loc (<- procs in)) 4))
           :in-theory (disable bake+-p suff-proc commit-proc
                               unfair-measure locs-for-not-queue
                               (:executable-counterpart
                                locs-for-not-queue)))))
)

;; END case 2

;; case 3: (and (memberp in queue)
;;              (not (memberp in locs))
;;              (equal in (first queue)))

(local
(defthm rank-keys-is-same-for-not-memberp
  (implies (and (suff-proc procs in bucket queue max)
                (not (memberp (loc (<- procs in)) (locs-for-not-queue)))
                (not (commit-proc (<- procs in))))
           (equal (sequence-measure (-> procs in
                                        (bake+-p (<- procs in) in procs max))
                                        keys (locs-for-not-queue))
                  (sequence-measure procs keys (locs-for-not-queue)))))
)

(local
(defthm unfair-measure-decreases-for-in=first-queue-1
  (implies (and (suff-proc procs in bucket queue max)
                (not (commit-proc (<- procs in)))
                (not (equal (loc (<- procs in)) 7))
                (not (equal (loc (<- procs in)) 8)))
           (msr< (unfair-measure (-> procs in (bake+-p (<- procs in) in procs
                                                       max))
                                 in)
                 (unfair-measure procs in)))
           :rule-classes :forward-chaining)
)

(local
(defthm unfair-measure-decreases-for-in=first-queue-2
  (implies (and (suff-proc procs in bucket queue max)
                (not (commit-proc (<- procs in)))
                (equal (loc (<- procs in)) 7)
                (not (choosing (<- procs (current (<- procs in))))))
           (msr< (unfair-measure (-> procs in (bake+-p (<- procs in) in procs
                                                       max))
                                 in)
                 (unfair-measure procs in)))
  :rule-classes :forward-chaining)
)

(local
(defthm unfair-measure-decreases-for-in=first-queue-3
  (implies (and (suff-proc procs in bucket queue max)
                (not (commit-proc (<- procs in)))
                (equal (loc (<- procs in)) 8)
                (not (pos (<- procs (current (<- procs in))))))
           (msr< (unfair-measure (-> procs in (bake+-p (<- procs in) in procs
                                                       max))
                                 in)
                 (unfair-measure procs in)))
  :rule-classes :forward-chaining)
)

(local
(defthm unfair-measure-decreases-for-in=first-queue-4
  (implies (and (suff-proc procs in bucket queue max)
                (not (commit-proc (<- procs in)))
                (equal (loc (<- procs in)) 8)
                (not (lex< (pos (<- procs (current (<- procs in))))
                           (current (<- procs in))
                           (pos (<- procs in))
                           in)))
           (msr< (unfair-measure (-> procs in (bake+-p (<- procs in) in procs
                                                       max))
                                 in)
                 (unfair-measure procs in)))
  :hints (("Goal"
           :in-theory (enable lex<)))
  :rule-classes :forward-chaining)
)

(local
(defthm unfair-measure-remains-for-loc-7
  (implies (and (choosing (<- procs (current (<- procs in))))
                (equal (loc (<- procs in)) 7))
           (equal (unfair-measure (-> procs in (bake+-p (<- procs in) in procs
                                                        max))
                                  in)
                  (unfair-measure procs in))))
)

(local
(defthm unfair-measure-remains-for-loc-8
  (implies (and (pos (<- procs (current (<- procs in))))
                (lex< (pos (<- procs (current (<- procs in))))
                      (current (<- procs in))
                      (pos (<- procs in))
                      in)
                (equal (loc (<- procs in)) 8))
           (equal (unfair-measure (-> procs in (bake+-p (<- procs in) in procs
                                                        max))
                                  in)
                  (unfair-measure procs in)))
  :hints (("Goal"
           :in-theory (enable lex<))))
)

(local
(defthm current-is-not-in-case-1
  (implies (lex< (pos (<- procs (current (<- procs in))))
                 (current (<- procs in))
                 (pos (<- procs in))
                 in)
           (not (equal (current (<- procs in)) in)))
  :hints (("Goal"
           :in-theory (enable lex<)))
  :rule-classes :forward-chaining)
)

(local
(defthm current-is-not-in-case-2
  (implies (and (suff-proc procs in bucket queue max)
                (equal (loc (<- procs in)) 7)
                (choosing (<- procs (current (<- procs in)))))
           (not (equal (current (<- procs in)) in)))
  :rule-classes :forward-chaining)
)

(local
(in-theory (disable locs-for-not-queue
                    (:executable-counterpart locs-for-not-queue)))
)

(local
(defthm unfair-measure-remains-same-for-first-queue-1
  (implies (and (suff-proc procs in bucket queue max)
                (not (commit-proc (<- procs in)))
                (equal (loc (<- procs in)) 7)
                (choosing (<- procs (current (<- procs in)))))
           (equal (unfair-measure (-> procs in (bake+-p (<- procs in) in procs
                                                        max))
                                  in)
                  (unfair-measure procs in)))
  :rule-classes :forward-chaining)
)

(local
(defthm unfair-measure-remains-same-for-first-queue-2
  (implies (and (suff-proc procs in bucket queue max)
                (not (commit-proc (<- procs in)))
                (equal (loc (<- procs in)) 8)
                (pos (<- procs (current (<- procs in))))
                (lex< (pos (<- procs (current (<- procs in))))
                      (current (<- procs in))
                      (pos (<- procs in))
                      in))
           (equal (unfair-measure (-> procs in (bake+-p (<- procs in) in procs
                                                        max))
                                  in)
                  (unfair-measure procs in))))
)

(local
(in-theory (disable g-keys-relationship))
)

(local
(defthm fair-suff-implies-current-member-of-select-1
  (implies (and (suff-proc procs in bucket queue max)
                (equal (loc (<- procs in)) 7)
                (my-subsetp (keys procs) (select-que env)))
           (memberp (current (<- procs in)) (select-que env)))
  :rule-classes :forward-chaining)
)

(local
(defthm fair-suff-implies-curr-member-of-select-2
  (implies (and (suff-proc procs in bucket queue max)
                (equal (loc (<- procs in)) 8)
                (my-subsetp (keys procs) (select-que env)))
           (memberp (current (<- procs in))
                    (select-que env)))
  :rule-classes :forward-chaining)
)

(local
(defthm unfair-measure-remains-same-if-does-not-move
  (implies (not (equal in a))
           (equal (unfair-measure (-> procs in (bake+-p (<- procs in) in procs
                                                        max))
                                  a)
                  (unfair-measure procs a))))
)

(local
(defthm loc-7-implies-current-is-same
  (implies (and (equal (loc p) 7)
                (choosing p))
           (equal (current (bake+-p p in procs max))
                  (current p))))
)

(local
(defthm loc-8-implies-current-is-same-1
  (implies (and (equal (loc p) 8)
                (not (pos (<- procs (current p)))))
           (equal (current (bake+-p p in procs max))
                  (current p))))
)

(local
(defthm loc-8-implies-current-is-same-2
  (implies (and (equal (loc p) 8)
                (lex< (pos (<- procs (current p)))
                      (current p)
                      (pos p)
                      in))
           (equal (current (bake+-p p in procs max))
                  (current p))))
)

(local
(defthm sequence-measure-is-natlistp
  (nat-listp (sequence-measure procs keys locs)))
)

(local
(defthm suff-proc-and-8-implies-pos
  (implies (and (suff-proc procs in bucket queue max)
		(equal (loc (<- procs in)) 8))
	   (pos (<- procs in)))
  :rule-classes :forward-chaining)
)

(local
(defthm rank-procs-decreases-for-first-queue
  (implies (and (suff-proc procs in bucket queue max)
                (not (commit-proc (<- procs in)))
                (consp queue)
                (equal in (car queue))
                (equal in (fair-select env X))
                (my-subsetp (keys procs) (select-que env))
                (not (memberp (loc (<- procs in)) (locs-for-not-queue))))
                (msr< (rank-procs (-> procs (first queue)
                                      (bake+-p (<- procs in) in
                                               procs max))
                             (keys procs)
                             queue
                             (fair-step env X)
                             (locs-for-not-queue))
                 (rank-procs procs (keys procs) queue env
			     (locs-for-not-queue))))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
	   :do-not-induct t
           :in-theory (disable bake+-p unfair-measure sequence-measure
                               suff-proc commit-proc)
           :cases ((and (not (equal (loc (<- procs (car queue))) 7))
                        (not (equal (loc (<- procs (car queue))) 8)))
                   (equal (loc (<- procs (car queue))) 7)
                   (equal (loc (<- procs (car queue))) 8)))
          ("Subgoal 2"
           :cases ((choosing (<- procs (current (<- procs (car queue)))))))
           ("Subgoal 2.1"
            :in-theory (disable commit-proc unfair-measure))
           ("Subgoal 2.1.2"
            :cases ((not (equal (g :current (g (car queue) procs))
                                (fair-select env x)))))
           ("Subgoal 2.1.2.1"
            :cases ((memberp (g :current (g (car queue) procs))
                             (select-que env))))

           ("Subgoal 2.1.1"
            :cases ((not (equal (g :current (g (car queue) procs))
                                (fair-select env x)))))
           ("Subgoal 2.1.1.1"
            :cases ((memberp (g :current (g (car queue) procs))
                             (select-que env))))

          ("Subgoal 1"
           :cases ((and (pos (<- procs (current (<- procs (car queue)))))
                        (lex< (pos (<- procs (current (<- procs (car queue)))))
                              (current (<- procs (car queue)))
                              (pos (<- procs (car queue)))
                              (car queue)))))))
)


;; END case 3

;;  case 4 : (and (memberp in queue)
;;               (not (memberp in locs))
;;               (not (equal in (first queue))))


(local
(defthm suff-and-not-memberp-locs-implies-not-choosing
  (implies (and (suff-proc procs in bucket queue max)
		(not (commit-proc (<- procs in)))
		(not (memberp (loc (<- procs in)) (locs-for-not-queue))))
	   (not (choosing (<- procs in))))
  :hints (("Goal"
	   :in-theory (enable locs-for-not-queue
			      (:executable-counterpart locs-for-not-queue))))
  :rule-classes :forward-chaining)
)

(local
(defthm suff-procs-to-bake+-not-choosing
  (implies (and (suff-proc procs in bucket queue max)
		(equal (loc (<- procs in)) 7))
	   (not (choosing (bake+-p (<- procs in) in procs max))))
  :rule-classes :forward-chaining)
)

(local
(defthm suff-proc-to-bake+-pos
  (implies (and (suff-proc procs in bucket queue max)
		(equal (loc (<- procs in)) 7))
	   (pos (bake+-p  (<- procs in) in procs max)))
  :rule-classes :forward-chaining)
)

(local
(defthm pos-is-same-for-7-and-8
  (implies (equal (loc p) 7)
	   (equal (pos (bake+-p p in procs max))
		  (pos p))))
)

(local
(defthm pos-if-7
  (implies (and (suff-proc procs in bucket queue max)
		(equal (loc (<- procs in)) 7))
	   (pos (<- procs in)))
  :rule-classes :forward-chaining)
)

(local
(defthm suff-procs-to-bake+-not-choosing-8
  (implies (and (suff-proc procs in bucket queue max)
		(equal (loc (<- procs in)) 8))
	   (not (choosing (bake+-p (<- procs in) in procs max))))
  :rule-classes :forward-chaining)
)

(local
(defthm suff-proc-to-bake+-pos-loc-8
  (implies (and (suff-proc procs in bucket queue max)
		(equal (loc (<- procs in)) 8))
	   (pos (bake+-p  (<- procs in) in procs max)))
  :rule-classes :forward-chaining)
)

(local
(defthm pos-is-same-for-8
  (implies (equal (loc p) 8)
	   (equal (pos (bake+-p p in procs max))
		  (pos p))))
)

(local
(defthm pos-if-8
  (implies (and (suff-proc procs in bucket queue max)
		(equal (loc (<- procs in)) 8))
	   (pos (<- procs in)))
  :rule-classes :forward-chaining)
)

(local
(defthm rank-procs-decreases-if-in-not-first-queue
  (implies (and (suff-proc procs in bucket queue max)
		(suff-proc procs (first queue) bucket queue max)
		(memberp (car queue) (select-que env))
		(memberp in (keys procs))
		(my-subsetp (keys procs) (select-que env))
		(lexicographic-pos procs queue)
		(memberp in queue)
                (not (commit-proc (<- procs in)))
                (not (equal in (first queue)))
                (equal in (fair-select env X))
                (not (memberp (loc (<- procs in)) (locs-for-not-queue))))
           (msr< (rank-procs (-> procs in (bake+-p (<- procs in) in procs max))
                             (keys procs)
                             queue
                             (fair-step env X)
                             (locs-for-not-queue))
                 (rank-procs procs (keys procs)
                             queue
                             env
                             (locs-for-not-queue))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (disable bake+-p suff-proc commit-proc unfair-measure
                               sequence-measure)
           :cases ((equal in (current (<- procs (first queue))))))
	  ("Subgoal 1"
	   :cases ((and (not (equal (loc (<- procs in)) 7))
			(not (equal (loc (<- procs in)) 8)))
		   (equal (loc (<- procs in)) 7)
		   (equal (loc (<- procs in)) 8)))
	  ("Subgoal 1.2"
	   :cases ((choosing (<- procs (current (<- procs in))))))
	  ("Subgoal 1.1"
	   :cases ((and (pos (<- procs (current (<- procs in))))
			(lex< (pos (<- procs (current (<- procs in))))
			      (current (<- procs in))
			      (pos (<- procs in))
			      in))))))
)

(local
(defthm memberp-to-consp
  (implies (memberp in queue)
	   (consp queue)))
)

(local
(in-theory (enable my-subsetp))
)

(local
(defthm subsetp-and-consp-implies-memberp
  (implies (and (my-subsetp queue keys)
		(my-subsetp keys select)
		(consp queue))
	   (memberp (first queue) select))
  :rule-classes :forward-chaining)
)

(local
(in-theory (disable rank-procs
		    memberp
		    bake+-p suff-proc unfair-measure commit-proc))
)

(local
(in-theory (disable pos=1+temp))
)

(local
(defthm rank-procs-decreases
  (implies (and (suff-proc procs in bucket queue max)
		(implies (consp queue)
			 (suff-proc procs (first queue) bucket queue max))
		(memberp in (keys procs))
		(my-subsetp queue (keys procs))
		(lexicographic-temp procs queue)
		(pos=1+temp procs queue)
		(equal in (fair-select env X))
		(my-subsetp (keys procs) (select-que env))
		(not (commit-proc (<- procs in))))
	   (msr< (rank-procs (-> procs in (bake+-p (<- procs in) in procs max))
			     (keys procs)
			     queue
			     (fair-step env X)
			     (locs-for-not-queue))
		 (rank-procs procs (keys procs) queue env
			     (locs-for-not-queue))))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize fertilize)
           :do-not-induct t
	   :cases ((and (not  (memberp in queue))
			(memberp (loc (<- procs in))
				 (locs-for-not-queue)))
		   (and (memberp in queue)
			(memberp (loc (<- procs in))
				 (locs-for-not-queue)))
		   (and (memberp in queue)
			(equal in (first queue))
			(not (memberp (loc (<- procs in))
				      (locs-for-not-queue))))
		   (and (memberp in queue)
			(not (equal in (first queue)))
			(not (memberp (loc (<- procs in))
				      (locs-for-not-queue))))))
          ("Subgoal 1"
           :in-theory (disable rank-procs-decreases-if-in-not-first-queue)
           :use ((:instance rank-procs-decreases-if-in-not-first-queue)))))
)

(local
(in-theory (disable rank-procs))
)

(local
(defthm suff-and-commit-implies-keys-same
  (implies (and (suff-proc procs in bucket queue max)
		(not (commit-proc (<- procs in))))
	   (equal (keys (-> procs in (bake+-p (<- procs in) in procs max)))
		  (keys procs)))
  :hints (("Goal"
	   :in-theory (enable suff-proc commit-proc g-keys-relationship
			      bake+-p))))
)

(local
(defthm suff-and-commit-implies-queue-same
  (implies (and (suff-proc procs in bucket queue max)
		(not (commit-proc (<- procs in))))
	   (equal (bake+-q (<- procs in) queue bucket max)
		  queue))
  :hints (("Goal"
	   :in-theory (enable suff-proc commit-proc))))
)

(local
(in-theory (disable my-subsetp lexicographic-temp rank-procs-decreases))
)

(local
(defthm not-commit-proc-implies-memberp-keys
  (implies (and (suff-proc procs in bucket queue max)
		(not (commit-proc (<- procs in))))
	   (memberp in (keys procs)))
  :hints (("Goal"
	   :in-theory (enable suff-proc commit-proc g-keys-relationship))))
)

(DEFTHM >>-stutter2-b-c
  (implies (and (fair-suff-b-c st X)
		(not (commit-b-c st (fair-select (env st) X))))
	   (msr< (rank-b-c (fair-bake+ st X))
		       (rank-b-c st)))
  :hints (("Goal"
	   :use ((:instance rank-procs-decreases
			    (procs (procs st))
			    (in (fair-select (env st) X))
			    (queue (queue st))
			    (bucket (bucket st))
			    (max (maxval st))
			    (env (env st))))))
  :rule-classes nil)
