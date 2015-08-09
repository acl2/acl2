(in-package "ACL2")

#|

  inv-persists.lisp
  ~~~~~~~~~~~~~~~~~

In this book, we prove one of the two big theorems in the bakery
implementation, viz., that invariants described in properties.lisp persist.
The formal statement we prove will be given by

(defthm inv-persists->>
  (implies (inv st)
           (inv (bake+ st in))))

We break down the proof into the proof of each of the predicates in inv, and
prove that each persists, assuming that all the invariants are true of the
current state. In fact, we have incrementally found the different invariants
from this approach. So we claim nothing about whether this is the minimal set
of invariants required to prove the theorems (I believe most probably not) but
this is actually a set of invariants that would be the "most" natural (at least
to me).

|#

(include-book "programs")
(include-book "properties")
(include-book "lexicographic-pos")


(set-case-split-limitations 'nil)

;; BEGIN persistence of natp max

(local
(defthm natp-max-persists-nil
  (implies (natp max)
	   (natp (bake+-max nil max))))
)

(local
(defthm natp-max-persists-non-nil
  (implies (and (inv-p-keys procs keys bucket queue max)
                (memberp in keys)
                (natp max))
           (natp (bake+-max (<- procs in) max))))
)

;; END persistence of natp max

;; BEGIN persistence of uniquep queue

(local
(defthm uniquep-q-persists-nil
  (implies (and (orderedp bucket)
		(disjoint bucket queue)
		(uniquep queue))
	   (uniquep (bake+-q nil queue bucket max))))
)

(local
(defthm orderedp-b-uniquep-queue-reduction
  (implies (and (uniquep bucket)
		(uniquep queue)
		(disjoint bucket queue))
	   (uniquep (append queue bucket)))
  :rule-classes :forward-chaining)
)

(local
(defthm uniquep-q-persists-non-nil
  (implies (and (orderedp bucket)
		(disjoint bucket queue)
		(uniquep queue))
	   (uniquep (bake+-q (<- procs in) queue bucket max))))
)

(local
(in-theory (disable orderedp-b-uniquep-queue-reduction))
)

;; END persistence  of uniquep queue

;; BEGIN persistence of orderedp bucket

(local
(defthm orderedp-b-persists-nil
  (implies (orderedp bucket)
	   (orderedp (bake+-b nil bucket in max))))
)

(local
(defthm orderedp-b-persists-non-nil
  (implies (orderedp bucket)
	   (orderedp (bake+-b  (<- procs in) bucket in max))))
)

;; END persistence of orderedp bucket

;; BEGIN persistence of b=max

(local
(defthm b=max-persists-nil
  (implies (and (b=max procs bucket max)
                (not (<- procs in)))
           (b=max (-> procs in (bake+-p nil in procs max))
                  (bake+-b nil bucket in max)
                  (bake+-max nil max)))
  :hints (("Subgoal *1/4"
           :cases ((equal in (car bucket))))))
)

(local
(defthm b=max-persists-non-nil-aux
  (implies (and (inv-p-p procs in bucket queue max)
                (b=max procs bucket max))
           (b=max (-> procs in (bake+-p (<- procs in) in procs max))
                  (bake+-b (<- procs in) bucket in max)
                  (bake+-max (<- procs in) max)))
  :hints (("Subgoal *1/2"
           :cases ((equal in (car bucket)))))
  :rule-classes nil)
)

(local
(defthm b=max-persists-non-nil
  (implies (and (inv-p-keys procs keys bucket queue max)
                (b=max procs bucket max)
                (memberp in keys))
           (b=max (-> procs in (bake+-p (<- procs in) in procs max))
                  (bake+-b (<- procs in) bucket in max)
                  (bake+-max (<- procs in) max)))
  :hints (("Goal"
           :in-theory (disable inv-p-keys
                               bake+-p bake+-b bake+-max)
           :use b=max-persists-non-nil-aux)))
)

;; END persistence of b=max

;; BEGIN persistence of q<max

(local
(defthm q<max-persists-nil
  (implies (and (q<max procs queue max)
                (not (<- procs in)))
           (q<max (-> procs in
                      (bake+-p nil in procs max))
                  (bake+-q nil queue bucket max)
                  (bake+-max nil max)))
  :hints (("Subgoal *1/4"
           :cases ((equal in (car queue))))))
)

(local
(defthm not-memberp-implies-q<max-persists
  (implies (not (memberp in queue))
	   (equal (q<max (-> procs in a) queue max)
		  (q<max procs queue max))))
)

(local
(defthm reduction-for-bucket
  (implies (b=max procs bucket max)
	   (q<max procs bucket (1+ max))))
)

(local
(defthm q<max-if-something-else-set
  (implies (equal (temp (<- (-> procs in a) in))
                  (temp (<- procs in)))
           (equal (q<max (-> procs in a) queue max)
                  (q<max procs queue max)))
  :hints (("Subgoal *1/3"
           :cases ((equal in (car queue))))
          ("Subgoal *1/2"
           :cases ((equal in (car queue))))))
)

(local
(defthm q<max-persists-non-nil-aux
  (implies (and (inv-p-p procs in bucket queue max)
		(q<max procs queue max)
		(b=max procs bucket max)
		(uniquep queue))
	   (q<max (-> procs in (bake+-p (<- procs in) in procs max))
		  (bake+-q (<- procs in) queue bucket max)
		  (bake+-max (<- procs in) max)))
  :hints (("Goal"
           :induct (q<max procs queue max))
          ("Subgoal *1/2"
           :cases ((not (equal in (car queue)))))))
)

(local
(defthm q<max-persists-non-nil
  (implies (and (inv-p-keys procs keys bucket queue max)
		(q<max procs queue max)
		(memberp in keys)
		(b=max procs bucket max)
		(uniquep queue))
	   (q<max (-> procs in (bake+-p (<- procs in) in procs max))
		  (bake+-q (<- procs in) queue bucket max)
		  (bake+-max (<- procs in) max)))
   :hints (("Goal"
	   :in-theory (disable inv-p-keys inv-p-p
			       bake+-p bake+-q bake+-max
			       uniquep b=max q<max))))
)

(local
(in-theory (disable reduction-for-bucket
                    q<max-if-something-else-set
                    q<max-persists-non-nil-aux))
)

;; END persitence of q<max


;; BEGIN persistence of choosing-bucket

(local
(defthm choosing-bucket-persists-non-nil-aux
  (implies (and (inv-p-p procs in bucket queue max)
		(choosing-bucket procs bucket))
	   (choosing-bucket (-> procs in
				(bake+-p (<- procs in) in procs max))
			    (bake+-b (<- procs in) bucket in max)))
  :hints (("Subgoal *1/2"
	   :cases ((equal in (car bucket))))))
)

(local
(defthm choosing-bucket-persists-non-nil
  (implies (and (inv-p-keys procs keys bucket queue max)
		(memberp in keys)
		(choosing-bucket procs bucket))
	   (choosing-bucket (-> procs in
				(bake+-p (<- procs in) in procs max))
			    (bake+-b (<- procs in) bucket in max)))
  :hints (("Goal"
	   :in-theory (disable inv-p-p
			       bake+-p bake+-b choosing-bucket))))
)

(local
(defthm choosing-bucket-persists-nil
  (implies (and (choosing-bucket procs bucket)
		(not (<- procs in)))
	   (choosing-bucket (-> procs in
				(bake+-p nil in procs max))
			    (bake+-b nil bucket in max)))
  :hints (("Subgoal *1/4"
	   :cases ((equal in (car bucket))))))
)

(local
(in-theory (disable choosing-bucket-persists-non-nil-aux))
)
;; END persistence of choosing-bucket

;; BEGIN persistence of choosing-pos

(local
(defthm choosing-pos-for-not-memberp
  (implies (not (memberp in queue))
	   (equal (choosing-pos (-> procs in a) queue)
		  (choosing-pos procs queue))))
)

(local
(defthm choosing-bucket-implies-choosing-pos
  (implies (choosing-bucket procs bucket)
	   (choosing-pos procs bucket)))
)

(local
(defthm choosing-pos-persists-for-bucket
  (implies (and (choosing-bucket procs bucket)
		(endp queue)
		(inv-p-p procs in bucket queue max))
	   (choosing-pos (-> procs in (bake+-p (<- procs in) in procs max))
			 (bake+-q (<- procs in) queue bucket max)))
  :hints (("Subgoal 2"
	   :do-not '(eliminate-destructors generalize fertilize))
	  ("Subgoal *1/5"
           :do-not '(eliminate-destructors generalize fertilize))
          ("Subgoal *1/5.1"
	   :cases ((equal in (car bucket))))
          ("Subgoal *1/5.3"
           :cases ((equal in (car bucket))))))
)

(local
(defthm choosing-pos-if-something-else-set
  (implies (and (equal (choosing p) (choosing (<- procs in)))
                (equal (pos p) (pos (<- procs in))))
           (equal (choosing-pos (-> procs in p) queue)
                  (choosing-pos procs queue)))
  :hints (("Goal"
           :induct (choosing-pos (-> procs in p) queue)
           :do-not-induct t)
          ("Subgoal *1/3"
           :cases ((equal in (car queue))))
          ("Subgoal *1/2"
           :cases ((equal in (car queue))))))
)

(local
(defthm choosing-pos-persists-non-nil-aux
  (implies (and (inv-p-p procs in bucket queue max)
		(choosing-pos procs queue)
		(uniquep queue)
		(natp max)
		(choosing-bucket procs bucket))
	   (choosing-pos (-> procs in
			     (bake+-p (<- procs in) in procs max))
			     (bake+-q (<- procs in) queue bucket max)))
  :hints (("Goal"
	  :induct (choosing-pos procs queue)
          :do-not-induct t)
	  ("Subgoal *1/2"
	   :cases ((not (equal in (car queue)))))
	  ("Subgoal *1/1"
	   :in-theory (disable choosing-pos-persists-for-bucket)
	   :use choosing-pos-persists-for-bucket)))
)

(local
(defthm choosing-pos-persists-non-nil
  (implies (and (inv-p-keys procs keys bucket queue max)
		(memberp in keys)
		(choosing-pos procs queue)
		(uniquep queue)
		(natp max)
		(choosing-bucket procs bucket))
	   (choosing-pos (-> procs in
			     (bake+-p (<- procs in) in procs max))
			     (bake+-q (<- procs in) queue bucket max)))
  :hints (("Goal"
	   :in-theory (disable inv-p-p
			       bake+-p bake+-q choosing-pos))))
)

(local
(defthm choosing-pos-persists-nil
  (implies (and (choosing-pos procs queue)
		(not (<- procs in)))
	   (choosing-pos (-> procs in
			     (bake+-p nil in procs max))
			     (bake+-q nil queue bucket max)))
  :hints (("Subgoal *1/4"
	   :cases ((equal in (car queue))))))
)

(local
(in-theory (disable choosing-pos-for-not-memberp
		    choosing-bucket-implies-choosing-pos
		    choosing-pos-persists-for-bucket
                    choosing-pos-if-something-else-set
		    choosing-pos-persists-non-nil-aux))
)

;; BEGIN persistence of subsetp bucket

(local
(in-theory (enable my-subsetp))
)

(local
(defthm insertion-preserves-my-subsetp
  (implies (my-subsetp a b)
	   (my-subsetp (insert in a) (insert in b))))
)

(local
(defthm my-subsetp-b-persists-non-nil
  (implies (and (my-subsetp bucket keys)
		(memberp in keys))
	   (my-subsetp (bake+-b (<- procs in) bucket in max)
		        keys)))
)

(local
(defthm my-subsetp-b-persists-nil
  (implies (my-subsetp bucket keys)
	   (my-subsetp (bake+-b nil bucket in max)
		        (insert in keys))))
)

;; END persistence of subsetp bucket

;; BEGIN persistence of subsetp queue

(local
(defthm my-subsetp-q-persists-non-nil-aux
  (implies (and (my-subsetp queue keys)
		(my-subsetp bucket keys))
	   (my-subsetp (bake+-q (<- procs in) queue bucket max)
		       keys)))
)

(local
(defthm my-subsetp-q-persists-non-nil
  (implies (and (my-subsetp queue keys)
		(my-subsetp bucket keys)
		(memberp in keys))
	   (my-subsetp (bake+-q (<- procs in) queue bucket max)
		        keys))
  :hints (("Goal"
	   :in-theory (disable bake+-q))))
)

(local
(defthm my-subsetp-q-persists-nil
  (implies (and (my-subsetp queue keys)
		(my-subsetp bucket keys))
	   (my-subsetp (bake+-q nil queue bucket max)
		       (insert in keys))))
)

(local
(in-theory (disable my-subsetp-q-persists-non-nil-aux))
)

;; BEGIN persistence of disjoint.

(local
(in-theory (enable disjoint intersect))
)

(local
(defthm disjoint-persists-non-nil
  (implies (and (inv-p-keys procs keys bucket queue max)
		(memberp in keys)
		(disjoint bucket queue))
	   (disjoint
	    (bake+-b (<- procs in) bucket in max)
	    (bake+-q (<- procs in) queue bucket max))))
)

(local
(defthm disjoint-persists-nil
  (implies (and (disjoint bucket queue)
		(not (<- procs in)))
	   (disjoint (bake+-b nil bucket in max)
		     (bake+-q nil queue bucket max))))
)

;; END persistence of disjoint

(local
(in-theory (disable disjoint intersect))
)

(local
(defthm legal-status-persists-itself-non-nil
  (implies (and (legal-status (<- procs in))
                (inv-p-p procs in bucket queue max))
           (legal-status (<- (-> procs in (bake+-p (<- procs in) in
                                                   procs max))
                             in))))
)

(local
(defthm legal-status-persists-others-non-nil
  (implies (and (legal-status (<- procs in))
                (legal-status (<- procs a))
                (not (equal a in)))
           (legal-status (<- (-> procs in (bake+-p (<- procs in)
                                                   in procs max))
                             a))))
)

(local
(in-theory (disable bake+-p inv-p-p legal-status))
)

(local
(defthm legal-status-list-for-not-member
  (implies (and (not (memberp in keys))
                (legal-status-listp keys procs))
           (legal-status-listp keys (-> procs in a))))
)

(local
(defthm legal-status-listp-persists-non-nil
  (implies (and (legal-status-listp keys procs)
                (inv-p-keys procs keys bucket queue max)
                (uniquep keys)
		(memberp in keys))
	   (legal-status-listp keys
			       (-> procs in
				   (bake+-p (<- procs in) in procs max))))
  :hints (("Goal"
          :induct (legal-status-listp keys
                                      (-> procs in
                                          (bake+-p (<- procs in) in procs
                                                   max)))
          :do-not-induct t)
          ("Subgoal *1/3"
           :cases ((equal in (car keys))))
          ("Subgoal *1/3.1"
           :in-theory (disable legal-status-persists-itself-non-nil)
           :use ((:instance legal-status-persists-itself-non-nil
                            (in (car keys)))))
          ("Subgoal *1/2"
           :cases ((equal in (car keys))))
          ("Subgoal *1/2.1"
           :in-theory (disable legal-status-persists-itself-non-nil)
           :use ((:instance legal-status-persists-itself-non-nil
                            (in (car keys)))))))
)

(local
(in-theory (enable legal-status inv-p-p bake+-p))
)

(local
(defthm legal-status-persists-itself-nil
  (implies (not (<- procs in))
           (legal-status (<- (-> procs in (bake+-p nil in procs max))
                             in))))
)

(local
(defthm legal-status-persists-others-nil
  (implies (and (legal-status (<- procs a))
                (not (equal a in)))
           (legal-status (<- (-> procs in (bake+-p nil in procs max))
                             a))))
)

(local
(defthm legal-status-insert-reduction
  (implies (and (legal-status-listp keys procs)
                (legal-status (<- procs in)))
           (legal-status-listp (insert in keys) procs)))
)

(local
(defthm legal-status-memberp-reduction
  (implies (and (legal-status-listp keys procs)
                (not (memberp in keys)))
           (legal-status-listp keys (-> procs in a))))

)

(local
(in-theory (disable legal-status))
)

(local
(defthm legal-status-listp-persists-nil-aux
  (implies (and (legal-status-listp keys procs)
                (not (memberp in keys))
                (not (<- procs in)))
	   (legal-status-listp (insert in keys)
			       (-> procs in
				   (bake+-p nil in procs max))))
  :hints (("Goal"
           :induct (legal-status-listp (insert in keys)
                                       (-> procs in
                                           (bake+-p nil in procs max))))))
)

(local
(defthm legal-status-listp-persists-nil
  (implies (and (legal-status-listp (keys procs) procs)
                (not (<- procs in)))
           (legal-status-listp (insert in (keys procs))
                               (-> procs in (bake+-p nil in procs max)))))
)

;; END persistence of legal-status-listp

;; BEGIN persistence of lexicographic-temp

(local
(defthm lexicographic-temp-persists-nil-aux
  (implies (and (lexicographic-temp procs queue)
                (not (memberp in queue))
                (not (<- procs in)))
           (lexicographic-temp (-> procs in (bake+-p nil in procs max))
                               (bake+-q nil queue bucket max)))
  :hints (("Subgoal *1/5"
           :cases ((equal in (car queue))))))
)

(local
(defun non-nil-indices (procs indices)
  (if (endp indices) T
    (and (<- procs (first indices))
         (non-nil-indices procs (rest indices)))))
)

(local
(defthm non-nil-to-non-member
  (implies (and (non-nil-indices procs keys)
                (not (<- procs in)))
           (not (memberp in keys)))
  :rule-classes :forward-chaining)
)

(local
(defthm lexicographic-temp-persists-nil
  (implies (and (lexicographic-temp procs queue)
                (non-nil-indices procs keys)
                (my-subsetp queue keys)
                (not (<- procs in)))
           (lexicographic-temp (-> procs in (bake+-p nil in procs max))
                               (bake+-q nil queue bucket max)))
  :hints (("Goal"
           :in-theory (disable bake+-p bake+-q))))
)

(local
(defthm lexicographic-temp-for-not-member
  (implies (not (memberp in queue))
           (equal (lexicographic-temp (-> procs in p) queue)
                  (lexicographic-temp procs queue))))
)

(local
(defthm b=max-q<max-implies-temp-<-for-queue
  (implies (and (b=max procs bucket max)
                (q<max procs queue max))
           (implies (and (memberp in bucket)
                         (memberp a queue))
                    (< (temp (<- procs a))
                       (temp (<- procs in))))))
)

(local
(defthm lexicographic-temp-if-something-else-set
  (implies (and (equal (temp p) (temp (<- procs in)))
                (uniquep queue))
           (equal (lexicographic-temp (-> procs in p) queue)
                  (lexicographic-temp procs queue)))
  :hints (("Subgoal *1/5"
           :cases ((equal in (car queue)) (equal in (cadr queue))))
          ("Subgoal *1/4"
           :cases ((equal in (car queue)) (equal in (cadr queue))))))
)

(local
(defthm lexicographic-append-reduction
  (implies (and (lexicographic-temp procs queue)
                (b=max procs bucket max)
                (q<max procs queue max)
                (orderedp bucket)
                (uniquep queue))
           (lexicographic-temp procs (append queue bucket)))
  :hints (("Goal"
           :in-theory (enable lex<)))
  :rule-classes :forward-chaining)
)

(local
(defthm lexicographic-temp-persists-non-nil-aux
  (implies (and (inv-p-p procs in bucket queue max)
                (lexicographic-temp procs queue)
                (b=max procs bucket max)
                (q<max procs queue max)
                (natp max)
                (orderedp bucket)
                (disjoint bucket queue)
                (uniquep queue))
           (lexicographic-temp (-> procs in (bake+-p (<- procs in) in procs
                                                     max))
                               (bake+-q (<- procs in) queue bucket max)))
; fcd/Satriani v3.7 Moore - used to be Subgoal 17
  :hints (("Subgoal 14"
            :in-theory (disable lexicographic-temp-if-something-else-set)
            :use ((:instance lexicographic-temp-if-something-else-set
                            (p (s :loc 4 (s :status 'wait (g in procs))))
                            (queue (append queue bucket)))
                 lexicographic-append-reduction
                 orderedp-b-uniquep-queue-reduction))))
)

(local
(defthm lexicographic-temp-persists-non-nil
  (implies (and (inv-p-keys procs keys bucket queue max)
                (memberp in keys)
                (lexicographic-temp procs queue)
                (b=max procs bucket max)
                (q<max procs queue max)
                (orderedp bucket)
                (natp max)
                (disjoint bucket queue)
                (uniquep queue))
           (lexicographic-temp (-> procs in (bake+-p (<- procs in) in procs
                                                     max))
                               (bake+-q (<- procs in) queue bucket max)))
  :hints (("Goal"
           :in-theory (disable inv-p-p inv-p-keys bake+-p bake+-q))))
)

;; END persistence of lexicographic-temp

(local
(in-theory (disable lexicographic-temp-persists-non-nil-aux
                    lexicographic-append-reduction
                    lexicographic-temp-if-something-else-set
                    b=max-q<max-implies-temp-<-for-queue
                    lexicographic-temp-for-not-member
                    lexicographic-temp-persists-nil-aux))
)

;; We also define the function lexicographic-pos here. We do not need
;; lexicographic-pos to persist by proving any explicit theorem, the
;; persistence of lexicographic-pos will be implied by persistence of
;; pos=1+temp and lexicographic-temp functions.

#|

(local
(defun lexicographic-pos-aux (procs queue)
  (if (endp queue) T
    (if (endp (rest queue)) T
      (and (lex< (pos (<- procs (first queue)))
		 (first queue)
		 (pos (<- procs (second queue)))
		 (second queue))
	   (lexicographic-pos-aux procs (rest queue))))))
)

(local
(defun lexicographic-pos (procs queue)
  (lexicographic-pos-aux procs (extract-indices-with-pos procs queue)))
)

|#

;; BEGIN persistence of inv-p-keys

(local
(defthm inv-p-p-preserves-others-nil
  (implies (and  (inv-p-p procs a bucket queue max)
		 (not (<- procs in))
		 (not (equal a in)))
	   (inv-p-p (-> procs in (bake+-p nil in procs max))
		    a
		    (bake+-b nil bucket in max)
		    (bake+-q nil queue bucket max)
		    (bake+-max nil max)))
  :hints (("Goal"
	   :cases ((equal (current (g a procs)) in)))))
)

(local
(in-theory (enable my-subsetp previous))
)

(local
(defthm inv-p-p-preserves-itself-nil
  (implies (and (non-nil-indices procs keys)
		(my-subsetp queue keys)
		(my-subsetp bucket keys)
		(not (<- procs in)))
	   (inv-p-p (-> procs in (bake+-p nil in procs max))
		    in
		    (bake+-b nil bucket in max)
		    (bake+-q nil queue bucket max)
		    (bake+-max nil max))))
)

(local
(defthm inv-p-p-preserves-others-non-nil
  (implies (and (inv-p-p procs in bucket queue max)
		(inv-p-p procs a bucket queue max)
		(not (equal a in)))
	   (inv-p-p (-> procs in (bake+-p (<- procs in) in procs max))
		    a
		    (bake+-b (<- procs in) bucket in max)
		    (bake+-q (<- procs in) queue bucket max)
		    (bake+-max (<- procs in) max)))
  :hints (("Goal"
	   :cases ((equal (current (g a procs)) in)))))
)

(local
(defthm choosing-pos-pos-reduction
  (implies (and (choosing-pos procs queue)
		(not (choosing (<- procs curr))))
	   (or (not (memberp curr queue))
	       (pos (<- procs curr))))
  :rule-classes nil)
)

(local
(defthm inv-p-p-preserves-itself-non-nil-aux
  (implies (and (inv-p-p procs in bucket queue max)
		(choosing-pos procs queue)
		(lexicographic-pos procs queue)
		(uniquep queue)
		(my-subsetp queue (keys procs))
		(natp max)
		(disjoint bucket queue))
	   (inv-p-p (-> procs in (bake+-p (<- procs in) in procs max))
		    in
		    (bake+-b (<- procs in) bucket in max)
		    (bake+-q (<- procs in) queue bucket max)
		    (bake+-max (<- procs in) max)))
  :hints (("Goal"
	   :do-not-induct t)
; fcd/Satriani v3.7 Moore - used to be Subgoal 8
	  ("Subgoal 7"
	   :cases ((equal in (current (<- procs in)))))
; fcd/Satriani v3.7 Moore - used to be Subgoal 4
	  ("Subgoal 6"
	   :use ((:instance choosing-pos-pos-reduction
			    (curr (current (<- procs in))))))
; fcd/Satriani v3.7 Moore - used to be Subgoal 2
	  ("Subgoal 4"
	   :use ((:instance choosing-pos-pos-reduction
			    (curr (current (<- procs in))))
		 (:instance lexicographic-pos-lex<-reduction
			    (curr (current (<- procs in))))))))
)

(local
(in-theory (disable inv-p-p bake+-p bake+-b bake+-q bake+-max
		    my-subsetp))
)

(local
(defthm inv-persists-insert-reduction
  (implies (and (inv-p-keys procs keys bucket queue max)
		(inv-p-p procs in bucket queue max))
	   (inv-p-keys procs (insert in keys) bucket queue max))
  :hints (("Goal"
	   :in-theory (disable inv-p-p))))
)

(local
(defthm non-nil-memberp-contrapositive
  (implies (and (non-nil-indices procs keys)
		(memberp a keys)
		(not (<- procs in)))
	   (not (equal a in))))
)

(local
(defthm inv-p-keys-preserved-nil-aux
  (implies (and (inv-p-keys procs keys bucket queue max)
		(non-nil-indices procs keys)
		(not (<- procs in)))
	   (inv-p-keys (-> procs in (bake+-p nil in procs max))
		       keys
		       (bake+-b nil bucket in max)
		       (bake+-q nil queue bucket max)
		       (bake+-max nil max)))
  :hints (("Subgoal *1/5"
	   :in-theory (disable inv-p-p-preserves-others-nil)
	   :use ((:instance inv-p-p-preserves-others-nil
			    (a (car keys)))))))
)

(local
(defthm inv-p-keys-preserved-nil
  (implies (and (inv-p-keys procs keys bucket queue max)
		(non-nil-indices procs keys)
		(my-subsetp queue keys)
		(my-subsetp bucket keys)
		(not (<- procs in)))
	   (inv-p-keys (-> procs in (bake+-p nil in procs max))
		       (insert in keys)
		       (bake+-b nil bucket in max)
		       (bake+-q nil queue bucket max)
		       (bake+-max nil max)))
  :hints (("Goal"
	  :in-theory (disable my-subsetp
			      inv-p-p non-nil-indices
			      bake+-p bake+-b bake+-q bake+-max))))
)

(local
(in-theory (disable lexicographic-pos))
)

(local
(defthm inv-p-keys-preserved-non-nil-aux-inv-p-p
  (implies (and (inv-p-keys procs keys bucket queue max)
		(lexicographic-pos procs queue)
		(choosing-pos procs queue)
		(memberp in keys)
		(memberp a keys)
		(uniquep queue)
		(my-subsetp queue (keys procs))
		(natp max)
		(disjoint bucket queue))
	   (inv-p-p (-> procs in (bake+-p (<- procs in) in procs max))
		    a
		    (bake+-b (<- procs in) bucket in max)
		    (bake+-q (<- procs in) queue bucket max)
		    (bake+-max (<- procs in) max)))
  :hints (("Subgoal *1/1"
	   :do-not-induct t
	   :cases ((equal in (car keys))))))
)

(local
(defthm inv-p-keys-preserved-non-nil-aux
  (implies (and (inv-p-keys procs keys bucket queue max)
		(memberp in keys)
		(lexicographic-pos procs queue)
		(choosing-pos procs queue)
		(uniquep queue)
		(my-subsetp queue (keys procs))
		(natp max)
		(disjoint bucket queue))
	   (inv-p-keys (-> procs in (bake+-p (<- procs in) in procs max))
		    keys
		    (bake+-b (<- procs in) bucket in max)
		    (bake+-q (<- procs in) queue bucket max)
		    (bake+-max (<- procs in) max)))
  :hints (("Goal"
	   :induct (inv-p-keys (-> procs in
				   (bake+-p (<- procs in) in procs max))
			       keys
			       (bake+-b (<- procs in) bucket in max)
			       (bake+-q (<- procs in) queue bucket max)
			       (bake+-max (<- procs in) max)))
	  ("Subgoal *1/2.2"
	   :cases ((equal in (car keys))))
          ("Subgoal *1/2.3"
           :cases ((equal in (car keys))))))
)

(local
(in-theory (enable my-subsetp))
)

(local
(defthm my-subsetp-implies-non-nil
  (implies (my-subsetp x (keys procs))
              (non-nil-indices procs x)))
)

(local
(defthm keys-are-non-nil
  (non-nil-indices procs (keys procs)))
)

(local
(in-theory (disable my-subsetp-implies-non-nil))
)

(local
(defthm inv-p-keys-persists
  (implies (and (inv-p-keys procs (keys procs) bucket queue max)
		(uniquep queue)
		(lexicographic-pos procs queue)
		(choosing-pos procs queue)
		(my-subsetp bucket (keys procs))
		(my-subsetp queue (keys procs))
		(natp max)
		(disjoint bucket queue))
	   (inv-p-keys (-> procs in (bake+-p (<- procs in) in procs max))
		    (insert in (keys procs))
		    (bake+-b (<- procs in) bucket in max)
		    (bake+-q (<- procs in) queue bucket max)
		    (bake+-max (<- procs in) max)))
  :hints (("Goal"
	   :do-not-induct t
	   :cases ((memberp in (keys procs)) (not (<- procs in))))
	  ("Subgoal 2"
	   :in-theory (disable g-keys-relationship))))
)


(local
(defthm procs-remain-forever
  (bake+-p p in procs max)
  :hints (("Goal"
           :in-theory (enable bake+-p))))
)

(local
(in-theory (disable inv-p-p inv-p-keys
		    disjoint legal-status-listp))
)

(local
(defthm my-subsetp-select-que-reduction
  (implies (my-subsetp keys (select-que env))
	   (my-subsetp keys (select-que (fair-step env X)))))
)

(local
(defthm memberp-and-subsetp-implies-subsetp-select
  (implies (and (memberp in select)
		(my-subsetp keys select))
	   (my-subsetp (insert in keys) select)))
)

(local
(defthm select-que-persists->>
  (implies (and (my-subsetp keys (select-que env))
		(equal in (fair-select env X)))
	   (my-subsetp (insert in keys)
		       (select-que (fair-step env X)))))
)

(local
(in-theory (disable my-subsetp
                    memberp-and-subsetp-implies-subsetp-select))
)

(DEFTHM inv-b-c-persists->>
  (implies (inv-b-c st)
	   (inv-b-c (bake+ st in)))
  :hints (("Goal"
           :cases ((memberp in (keys (procs st))) (not (<- (procs st) in))))
	  ("Subgoal 2"
	   :in-theory (disable g-keys-relationship))
          ("Subgoal 1"
           :in-theory (disable keys-are-non-nil)
           :use ((:instance keys-are-non-nil
                            (procs (procs st))))))
  :rule-classes nil)

(DEFTHM fair-inv-b-c-persists->>
  (implies (fair-inv-b-c st)
           (fair-inv-b-c (fair-bake+ st X)))
  :hints (("Goal"
           :cases ((memberp (fair-select (env st) X) (keys (procs st)))
                   (not (<- (procs st) (fair-select (env st) X)))))
          ("Subgoal 2"
           :in-theory (disable g-keys-relationship))
          ("Subgoal 1"
           :in-theory (disable keys-are-non-nil)
           :use ((:instance keys-are-non-nil
                            (procs (procs st))))))
  :rule-classes nil)

(local
(defthm inv-p-p-c-s-persists-itself-non-nil-not-go
  (implies (and (inv-p-p-c-s procs in bucket queue nil)
                in)
           (inv-p-p-c-s (-> procs in (cent-p (<- procs in) queue in))
                        in
                        (cent-b (<- procs in) bucket in)
                        (cent-q (<- procs in) queue in bucket)
                        (cent-go (<- procs in) nil queue in)))
  :hints (("Goal"
           :do-not-induct t)))
)

(local
(defthm inv-p-p-c-s-persists-itself-non-nil-go
  (implies (and (inv-p-p-c-s procs in bucket queue go)
                (go-queue go  queue)
                (uniquep queue)
                (disjoint bucket queue)
                in
                (equal in go))
           (inv-p-p-c-s (-> procs in (cent-p (<- procs in) queue in))
                        in
                        (cent-b (<- procs in) bucket in)
                        (cent-q (<- procs in) queue in bucket)
                        (cent-go (<- procs in) go queue in)))
  :hints (("Goal"
           :do-not-induct t)))
)

(local
(in-theory (enable my-subsetp))
)

(local
(defthm non-nil-subset-reduction
  (implies (and (non-nil-indices procs keys)
                (my-subsetp queue keys))
           (non-nil-indices procs queue))
  :rule-classes :forward-chaining)
)

(local
(defthm inv-p-p-persists-itself-nil-not-go
  (implies (and (not (<- procs in))
                (not (memberp in queue))
                (non-nil-indices procs keys)
                (my-subsetp bucket keys)
                in)
           (inv-p-p-c-s (-> procs in (cent-p nil queue in))
                        in
                        (cent-b nil bucket in)
                        (cent-q nil queue in bucket)
                        (cent-go nil nil queue in)))
  :hints (("Goal"
           :do-not-induct t)))
)

(local
(defthm inv-p-p-persists-itself-nil-go
  (implies (and (not (<- procs in))
                (keys-not-nil queue)
                (non-nil-indices procs keys)
                (my-subsetp queue keys)
                (my-subsetp bucket keys)
                ;;(non-nil-indices procs queue)
                ;; (non-nil-indices procs bucket)
                in)
           (inv-p-p-c-s (-> procs in (cent-p nil queue in))
                        in
                        (cent-b nil bucket in)
                        (cent-q nil queue in bucket)
                        (cent-go nil nil queue in))))
)

(local
(defthm inv-p-p-persists-others-non-nil-not-go
  (implies (and (inv-p-p-c-s procs in bucket queue nil)
                (inv-p-p-c-s procs a bucket queue nil)
                (not (equal in a))
                in a)
           (inv-p-p-c-s (-> procs a (cent-p (<- procs a) queue a))
                        in
                        (cent-b (<- procs a) bucket a)
                        (cent-q (<- procs a) queue a bucket)
                        (cent-go (<- procs a) nil queue a))))
)

(local
(defthm inv-p-p-persists-others-non-nil-go
  (implies (and (inv-p-p-c-s procs in bucket queue go)
                (not (equal in a))
                in a
                (disjoint bucket queue)
                (go-queue go queue)
                (equal a go))
           (inv-p-p-c-s (-> procs a (cent-p (<- procs a) queue a))
                        in
                        (cent-b (<- procs a) bucket a)
                        (cent-q (<- procs a) queue a bucket)
                        (cent-go (<- procs a) go queue a))))
)

(local
(defthm inv-p-p-persists-others-nil
  (implies (and (inv-p-p-c-s procs in bucket queue go)
                (not (equal in a))
                (not (<- procs a)))
            (inv-p-p-c-s (-> procs a (cent-p nil queue a))
                        in
                        (cent-b nil bucket a)
                        (cent-q nil queue a bucket)
                        (cent-go nil go queue a))))
)

(local
(in-theory (disable inv-p-p-c-s cent-p cent-b cent-q cent-go))
)

(local
(defthm inv-p-keys-c-s-implies-inv-p-p
  (implies (and (inv-p-keys-c-s procs keys bucket queue go)
                (memberp in keys))
           (inv-p-p-c-s procs in bucket queue go))
  :rule-classes :forward-chaining)
)

(local
(defthm inv-insert
  (implies (and (inv-p-keys-c-s procs keys bucket queue go)
                (force (inv-p-p-c-s procs in bucket queue go)))
           (inv-p-keys-c-s procs (insert in keys) bucket queue go)))
)

(local
(defthm inv-p-keys-c-s-persists-nil-not-go
  (implies (and (inv-p-keys-c-s procs keys bucket queue nil)
                (not (<- procs in))
                in
                (keys-not-nil keys)
                (non-nil-indices procs keys))
           (inv-p-keys-c-s (-> procs in (cent-p nil queue in))
                           keys
                           (cent-b nil bucket in)
                           (cent-q nil queue in bucket)
                           (cent-go nil nil queue in)))
  :hints (("Subgoal *1/6"
           :cases ((equal in (car keys))))))
 )

(local
(defthm inv-p-keys-c-s-persists-non-nil-not-go-itself
  (implies (and (inv-p-keys-c-s procs keys bucket queue nil)
                (memberp in keys)
                in)
           (inv-p-p-c-s (-> procs in (cent-p (<- procs in) queue in))
                        in
                        (cent-b (<- procs in) bucket in)
                        (cent-q (<- procs in) queue in bucket)
                        (cent-go (<- procs in) nil queue in))))
)

(local
(defthm keys-not-nil-member-implies-not-nil
  (implies (and (memberp in keys)
                (keys-not-nil keys))
           in)
  :rule-classes :forward-chaining)
)

(local
(defthm inv-p-keys-persists-others-non-nil-go
  (implies (and (inv-p-keys-c-s procs keys bucket queue go)
                (memberp in keys)
                (keys-not-nil keys)
                a go
                (uniquep queue)
                (disjoint bucket queue)
                (not (equal in a))
                (go-queue go queue)
                (equal a go))
           (inv-p-p-c-s (-> procs a (cent-p (<- procs a) queue a))
                        in
                        (cent-b (<- procs a) bucket a)
                        (cent-q (<- procs a) queue a bucket)
                        (cent-go (<- procs a) go queue a))))
)

(local
(defthm inv-p-keys-persists-others-non-nil-not-go-aux
  (implies (and (inv-p-keys-c-s procs keys bucket queue nil)
                (memberp in keys)
                (memberp a keys)
                (uniquep keys)
                (keys-not-nil keys)
                a
                (not (equal in a)))
           (inv-p-p-c-s (-> procs a (cent-p (<- procs a) queue a))
                        in
                        (cent-b (<- procs a) bucket a)
                        (cent-q (<- procs a) queue a bucket)
                        (cent-go (<- procs a) nil queue a)))
  :hints (("Subgoal *1/3"
           :cases ((not (equal a (car keys)))))))
)

(local
(defthm inv-p-keys-persists-others-non-nil-not-go
  (implies (and (inv-p-keys-c-s procs keys bucket queue nil)
                (memberp a keys)
                (uniquep queue)
                (disjoint bucket queue)
                (uniquep keys)
                (keys-not-nil keys))
           (inv-p-keys-c-s (-> procs a (cent-p (<- procs a) queue a))
                        keys
                        (cent-b (<- procs a) bucket a)
                        (cent-q (<- procs a) queue a bucket)
                        (cent-go (<- procs a) nil queue a)))
  :hints (("Subgoal *1/3"
           :cases ((not (equal a (car keys)))))))
)

(local
(in-theory (disable keys-are-non-nil))
)

(local
(defthm inv-p-keys-c-s-persists-not-go
  (implies (and (inv-p-keys-c-s procs (keys procs) bucket queue nil)
                (keys-not-nil (keys procs))
                (my-subsetp queue (keys procs))
                (my-subsetp bucket (keys procs))
                (uniquep queue)
                (disjoint bucket queue)
                a)
           (inv-p-keys-c-s (-> procs a (cent-p (<- procs a) queue a))
                           (insert a (keys procs))
                           (cent-b (<- procs a) bucket a)
                           (cent-q (<- procs a) queue a bucket)
                           (cent-go (<- procs a) nil queue a)))
  :hints (("Goal"
           :in-theory (disable inv-p-keys)
           :use keys-are-non-nil)
          ("Goal'"
           :cases ((memberp a (keys procs)) (not (<- procs a))))
          ("Subgoal 2"
           :in-theory (disable g-keys-relationship))
          ("[1]Goal"
           :in-theory (disable non-nil-subset-reduction)
           :use ((:instance non-nil-subset-reduction
                            (keys (keys procs)))
                 (:instance non-nil-subset-reduction
                            (keys (keys procs))
                            (queue bucket))))))
)


(local
(defthm inv-p-keys-c-s-persists-nil-go
  (implies (and (inv-p-keys-c-s procs keys bucket queue go)
                (not (<- procs in))
                (go-queue go queue)
                in
                (equal in go)
                (keys-not-nil keys)
                (non-nil-indices procs keys))
           (inv-p-keys-c-s (-> procs in (cent-p nil queue in))
                           keys
                           (cent-b nil bucket in)
                           (cent-q nil queue in bucket)
                           (cent-go nil go queue in)))
  :hints (("Subgoal *1/6"
           :cases ((equal in (car keys))))
          ("Subgoal *1/3"
           :cases ((equal in (car keys))))))
 )

(local
(defthm inv-p-keys-c-s-persists-non-nil-go-itself
  (implies (and (inv-p-keys-c-s procs keys bucket queue go)
                (memberp in keys)
                (equal in go)
                (uniquep queue)
                (disjoint bucket queue)
                (go-queue go queue)
                in)
           (inv-p-p-c-s (-> procs in (cent-p (<- procs in) queue in))
                        in
                        (cent-b (<- procs in) bucket in)
                        (cent-q (<- procs in) queue in bucket)
                        (cent-go (<- procs in) go queue in))))
)

(local
(defthm keys-not-nil-member-implies-not-nil
  (implies (and (memberp in keys)
                (keys-not-nil keys))
           in)
  :rule-classes :forward-chaining)
)

(local
(defthm inv-p-keys-persists-others-non-nil-go
  (implies (and (inv-p-keys-c-s procs keys bucket queue go)
                (memberp in keys)
                (keys-not-nil keys)
                a go
                (uniquep queue)
                (disjoint bucket queue)
                (not (equal in a))
                (go-queue go queue)
                (equal a go))
           (inv-p-p-c-s (-> procs a (cent-p (<- procs a) queue a))
                        in
                        (cent-b (<- procs a) bucket a)
                        (cent-q (<- procs a) queue a bucket)
                        (cent-go (<- procs a) go queue a))))
)

(local
(defthm inv-p-keys-persists-others-non-nil-go-aux
  (implies (and (inv-p-keys-c-s procs keys bucket queue go)
                (memberp in keys)
                (memberp a keys)
                (uniquep queue)
                (disjoint bucket queue)
                (keys-not-nil keys)
                a
                (go-queue go queue)
                (equal a go)
                (not (equal in a)))
           (inv-p-p-c-s (-> procs a (cent-p (<- procs a) queue a))
                        a
                        (cent-b (<- procs a) bucket a)
                        (cent-q (<- procs a) queue a bucket)
                        (cent-go (<- procs a) go queue a))))

)



(local
(defthm inv-p-keys-persists-others-non-nil-go-final
  (implies (and (inv-p-keys-c-s procs keys bucket queue go)
                (memberp a keys)
                (uniquep queue)
                (equal a go)
                (go-queue go queue)
                (disjoint bucket queue)
                (uniquep keys)
                (keys-not-nil keys))
           (inv-p-keys-c-s (-> procs a (cent-p (<- procs a) queue a))
                        keys
                        (cent-b (<- procs a) bucket a)
                        (cent-q (<- procs a) queue a bucket)
                        (cent-go (<- procs a) go queue a)))
  :hints (("Subgoal *1/3.1"
           :cases ((equal (car queue) (car keys)))))))


(local
(in-theory (disable keys-are-non-nil))
)

(local
(defthm inv-p-keys-c-s-persists-go
  (implies (and (inv-p-keys-c-s procs (keys procs) bucket queue go)
                (keys-not-nil (keys procs))
                (my-subsetp queue (keys procs))
                (my-subsetp bucket (keys procs))
                (go-queue go queue)
                (uniquep queue)
                (disjoint bucket queue)
                (equal a go)
                a)
            (inv-p-keys-c-s (-> procs a (cent-p (<- procs a) queue a))
                            (insert a (keys procs))
                            (cent-b (<- procs a) bucket a)
                            (cent-q (<- procs a) queue a bucket)
                            (cent-go (<- procs a) go queue a)))
  :hints (("Goal"
           :in-theory (disable inv-p-keys)
           :use keys-are-non-nil)
          ("Goal'"
           :cases ((memberp a (keys procs)) (not (<- procs a))))
          ("Subgoal 2"
           :in-theory (disable g-keys-relationship))
          ("[1]Goal"
           :in-theory (disable non-nil-subset-reduction)
           :use ((:instance non-nil-subset-reduction
                            (keys (keys procs)))
                 (:instance non-nil-subset-reduction
                            (keys (keys procs))
                            (queue bucket))))))
)

(local
(defthm not-nil-persists
  (implies (and (keys-not-nil keys)
                in)
           (keys-not-nil (insert in keys))))
)

(local
(in-theory (enable cent-b cent-q cent-go inv-p-p-c-s))
)

(local
(defthm go-queue-persists-not-go-non-nil
  (go-queue (cent-go (<- procs in) nil queue in)
            (cent-q  (<- procs in) queue in bucket)))
)

(local
(defthm go-queue-persists-not-go-nil
  (go-queue (cent-go nil nil queue in)
            (cent-q  nil queue in bucket)))
)

(local
(defthm go-queue-persists-go
  (implies (and (inv-p-keys-c-s procs keys bucket queue go)
                (memberp in keys)
                go
                (equal in go))
           (go-queue (cent-go (<- procs in) go queue  in)
                     (cent-q  (<- procs in) queue in bucket))))
)

(local
(defthm go-queue-persists-go-nil
  (implies (and  go
                 (go-queue go queue)
                (equal in go))
           (go-queue (cent-go nil go queue  in)
                     (cent-q  nil queue in bucket))))
)

(local
(in-theory (disable go-queue))
)

(local
(defthm ordered-b-persists-non-nil
  (implies (and (inv-p-keys-c-s procs keys bucket queue go)
                (memberp in keys)
                (orderedp bucket))
           (orderedp (cent-b (<- procs in) bucket in))))
)

(local
(defthm ordered-b-persists-nil
  (implies (and (not (<- procs in))
                (orderedp bucket))
           (orderedp (cent-b nil bucket in))))
)

(local
(in-theory (enable orderedp-b-uniquep-queue-reduction))
)

(local
(defthm uniquep-q-persists-nil-c-s
  (implies (and (orderedp bucket)
		(disjoint bucket queue)
		(uniquep queue))
	   (uniquep (cent-q nil queue in bucket))))
)

(local
(defthm uniquep-q-persists-non-nil-c-s
  (implies (and (orderedp bucket)
		(disjoint bucket queue)
		(uniquep queue))
	   (uniquep (cent-q (<- procs in) queue in bucket))))
)

(local
(in-theory (enable disjoint intersect))
)

(local
(defthm disjoint-persists-non-nil-c-s
  (implies (and (inv-p-keys-c-s procs keys bucket queue max)
		(memberp in keys)
		(disjoint bucket queue))
	   (disjoint
	    (cent-b (<- procs in) bucket in)
	    (cent-q (<- procs in) queue in bucket))))
)

(local
(defthm disjoint-persists-nil-c-s
  (implies (and (disjoint bucket queue)
		(not (<- procs in)))
	   (disjoint (cent-b nil bucket in)
		     (cent-q nil queue in bucket))))
)


(local
(defthm my-subsetp-b-persists-non-nil-c-s
  (implies (and (my-subsetp bucket keys)
		(memberp in keys))
	   (my-subsetp (cent-b (<- procs in) bucket in)
		        keys)))
)

(local
(defthm my-subsetp-b-persists-nil-c-s
  (implies (my-subsetp bucket keys)
	   (my-subsetp (cent-b nil bucket in)
		        (insert in keys))))
)

;; END persistence of subsetp bucket

;; BEGIN persistence of subsetp queue

(local
(defthm my-subsetp-q-persists-non-nil-aux-c-s
  (implies (and (my-subsetp queue keys)
		(my-subsetp bucket keys))
	   (my-subsetp (cent-q (<- procs in) queue in bucket)
		       keys)))
)

(local
(defthm my-subsetp-q-persists-non-nil-c-s
  (implies (and (my-subsetp queue keys)
		(my-subsetp bucket keys)
		(memberp in keys))
	   (my-subsetp (cent-q (<- procs in) queue in bucket)
		        keys))
  :hints (("Goal"
	   :in-theory (disable cent-q))))
)

(local
(defthm my-subsetp-q-persists-nil-c-s
  (implies (and (my-subsetp queue keys)
		(my-subsetp bucket keys))
	   (my-subsetp (cent-q nil queue in bucket)
		       (insert in keys))))
)

(local
(in-theory (disable my-subsetp-q-persists-non-nil-aux-c-s))
)

(local
(in-theory (disable disjoint intersect))
)

(local
(in-theory (disable cent-p cent-b cent-q cent-go))
)

(local
(defthm keys-of-cent-is-insert
  (equal (keys (-> procs in (cent-p (<- procs in) queue in)))
         (insert in (keys procs)))
  :hints (("Goal"
           :in-theory (enable cent-p))))
)

(local
(in-theory (disable memberp-yes-reduce-insert))
)

(local
(defthm procs-for-cent
  (cent-p p queue in)
  :hints (("Goal"
           :in-theory (enable cent-p))))
)

(local
(in-theory (disable non-nil-to-non-member inv-p-p-c-s inv-p-keys-c-s))
)

(local
(in-theory (enable keys-are-non-nil))
)

(local
(defthm null-process-not-in-queue
  (implies (and (my-subsetp queue (keys procs))
                (not (<- procs in)))
           (not (memberp in queue)))
  :rule-classes nil)
)

(local
(defthm go-has-procs
  (implies (and (non-nil-indices procs keys)
                (my-subsetp queue keys)
                (go-queue go queue)
                go)
           (<- procs go))
  :hints (("Goal"
           :in-theory (enable go-queue)))
  :rule-classes nil)
)

(local
(in-theory (enable cent-p cent-go))
)

(local
(defthm go-procs-persists-not-go-non-nil
  (implies (and (go-procs go procs)
                (not go))
           (go-procs (cent-go (<- procs in) nil queue in)
                     (-> procs in (cent-p (<- procs in) queue in))))
  :hints (("Goal"
           :do-not-induct t)))
)

(local
(defthm go-procs-persists-not-go-nil
  (implies (and (go-procs go procs)
                (not go))
           (go-procs (cent-go nil nil queue in)
                     (-> procs in (cent-p nil queue in))))
  :hints (("Goal"
           :do-not-induct t)))
)

(local
(defthm go-procs-for-go-non-nil
  (implies (and (go-procs go procs)
                (equal in go))
           (go-procs (cent-go (<- procs in) go queue in)
                     (-> procs in (cent-p (<- procs in) queue in))))
  :hints (("Goal"
           :do-not-induct t)))
)

(local
(defthm go-procs-for-go-nil
  (implies (and (not (<- procs in))
                (go-procs go procs)
                (equal in go))
           (go-procs (cent-go nil go queue in)
                     (-> procs in (cent-p nil queue in))))
  :hints (("Goal"
           :do-not-induct t)))
)

(local
(in-theory (disable cent-p cent-go go-procs))
)

(DEFTHM inv-c-s-persists->>
  (implies (and (inv-c-s st)
                (legal st in))
           (inv-c-s (cent st in)))
  :hints (("Goal"
           :do-not-induct t
           :cases ((and (not (get-go st))
                        (memberp in (keys (procs st))))
                   (and (get-go st)
                        (equal (get-go st) in)
                        (memberp in (keys (procs st))))
                   (and (not (get-go st))
                        (not (<- (procs st) in)))
                   (and (get-go st)
                        (equal (get-go st) in)
                        (not (<- (procs st) in)))))
          ("Subgoal 4"
           :in-theory (disable g-keys-relationship))
          ("Subgoal 3"
           :in-theory (disable go-procs-for-go-non-nil
                               g-keys-relationship)
           :use ((:instance go-procs-for-go-non-nil
                            (procs (procs st))
                            (queue (queue st))
                            (go (get-go st)))))

          ("[1]Subgoal 1" ; # changed by Matt K. for cons-tag-trees mod (v3-2)
           :in-theory (disable go-procs-for-go-non-nil
                               inv-p-p-persists-itself-nil-not-go)
           :use ((:instance null-process-not-in-queue
                            (procs (procs st))
                            (queue (queue st)))
                 (:instance inv-p-p-persists-itself-nil-not-go
                            (procs (procs st))
                            (keys (keys (procs st)))
                            (queue (queue st))
                            (bucket (bucket st)))))
          ("[1]Subgoal 2" ; # changed by Matt K. for cons-tag-trees mod (v3-2)
           :in-theory (disable keys-are-non-nil)
           :use ((:instance keys-are-non-nil
                            (procs (procs st)))
                 (:instance go-has-procs
                            (procs (procs st))
                            (keys (keys (procs st)))
                            (queue (queue st))
                            (go (get-go st))))))
  :rule-classes nil)







