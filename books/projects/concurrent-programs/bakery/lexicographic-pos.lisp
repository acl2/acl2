(in-package "ACL2")



(include-book "properties")
(include-book "pos-temp")


(defun lexicographic-pos-aux (procs queue)
  (if (endp queue) T
    (if (endp (rest queue)) T
      (and (lex< (pos (<- procs (first queue)))
		 (first queue)
		 (pos (<- procs (second queue)))
		 (second queue))
	   (lexicographic-pos-aux procs (rest queue))))))

(defun lexicographic-pos (procs queue)
  (lexicographic-pos-aux procs (extract-indices-with-pos procs queue)))

(local
(defthm memberp-lexicographic-temp-reduction
  (implies (and (lexicographic-temp procs queue)
                (memberp y (cdr queue)))
           (lex< (temp (<- procs (car queue)))
                 (car queue)
                 (temp (<- procs y))
                 y)))
)

(local
(defthm car-of-extract-indices-is-a-member-of-queue
  (implies (consp (extract-indices-with-pos procs queue))
           (memberp (car (extract-indices-with-pos procs queue))
                    queue)))
)

(local
(defthm lexicographi-temp-extract-indices-reduction
  (implies (lexicographic-temp procs queue)
           (lexicographic-temp procs (extract-indices-with-pos procs queue)))
  :rule-classes :forward-chaining)
)

(local
(in-theory (enable my-subsetp previous))
)

(local
(defthm extract-preserved-by-previous
  (implies (and (pos (<- procs in))
                (pos (<- procs curr)))
           (equal (memberp curr (previous (extract-indices-with-pos procs queue)
                                          in))
                  (memberp curr (previous queue in))))
  :rule-classes nil)
)


(local
(defthm lexicographic-pos-aux-lex<-reduction
  (implies (and (lexicographic-pos-aux procs queue)
                (memberp in queue)
                (not (lex< (pos (<- procs curr))
                           curr
                           (pos (<- procs in))
                           in)))
           (not (memberp curr (previous queue in))))
  :rule-classes nil)
)

(local
(defthm memberp-extract-reduction
  (implies (pos (<- procs in))
           (equal (memberp in (extract-indices-with-pos procs queue))
                  (memberp in queue)))
  :rule-classes nil)
)


(local
(in-theory (disable memberp-lexicographic-temp-reduction
                    car-of-extract-indices-is-a-member-of-queue))
)

(local
(defthm pos=1+temp-lexicographic-pos-aux-reduction
  (implies (and (lexicographic-temp procs queue)
                (pos=1+temp-aux procs queue))
           (lexicographic-pos-aux procs queue)))
)

(local
(in-theory (disable lexicographic-pos-aux
                    pos=1+temp-aux))
)

(defthm pos=1+temp-lex-pos-lex-temp-reduction
  (implies (and (pos=1+temp procs queue)
                (lexicographic-temp procs queue))
           (lexicographic-pos procs queue))
  :rule-classes :forward-chaining)

(defthm lexicographic-pos-lex<-reduction
  (implies (and (lexicographic-pos procs queue)
		(pos (<- procs curr))
		(pos (<- procs in))
		(not (lex< (pos (<- procs curr))
			   curr
			   (pos (<- procs in))
                           in ))
		(memberp in queue))
	   (not (memberp curr (previous queue in))))
  :hints (("Goal"
           :use ((:instance lexicographic-pos-aux-lex<-reduction
                            (queue (extract-indices-with-pos procs queue)))
                 memberp-extract-reduction
                 extract-preserved-by-previous))))

(in-theory (disable lexicographic-pos))

(local
(defthm car-queue-previous-reduction
  (implies (and (memberp in queue)
                (not (equal in (car queue))))
           (memberp (car queue) (previous queue in)))
  :hints (("Goal"
           :expand (previous queue in))))
)

(defthm lexicographic-pos-implies-everything-<-car-queue
  (implies (and (lexicographic-pos procs queue)
                (pos (<- procs (car queue)))
                (pos (<- procs in))
                (lex< (pos (<- procs in))
                      in
                      (pos (<- procs (car queue)))
                      (car queue)))
           (not (memberp in queue)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable lexicographic-pos-lex<-reduction)
           :use ((:instance lexicographic-pos-lex<-reduction
                            (curr (car queue)))))
          ("Goal'"
           :cases ((equal in (car queue))))
          ("Subgoal 1"
           :in-theory (enable lex<))))
