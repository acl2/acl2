(in-package "DM")

(include-book "projects/groups/lists" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

;; A formalization of Euler's analysis of the 7 Bridges of Konigsberg
;; (https://en.wikipedia.org/wiki/Seven_Bridges_of_Königsberg).

; There are 4 regions, 2 of which are islands:

(defun regions () '(l1 l2 i1 i2))

;; There are 7 bridges:

(defun bridges () '(b1 b2 b3 b4 b5 b6 b7))

(defun town ()
  '((b1 l1 i1) (b2 l1 i1) (b3 l1 i2) ;2 bridges between l1 and i1, 1 between l1 and i2
    (b4 l2 i1) (b5 l2 i1) (b6 l2 i2) ;2 bridges between l2 and i1, 1 between l2 and i2
    (b7 i1 i2)))                     ;1 bridge between i1 and i2

;; b is a bridge that connects region r to some other region:

(defun bridgep (b r)
  (and (member-equal b (bridges))
       (or (equal r (cadr (assoc b (town))))
	   (equal r (caddr (assoc b (town)))))))

;; The region to which b connects r:

(defun next (b r)
  (let ((step (assoc b (town))))
    (if (equal r (cadr step))
	(caddr step)
      (cadr step))))

;; A path is represented by a starting point and a list of bridges:

(defun pathp (p r)
  (if (consp p)
      (and (bridgep (car p) r)
	   (pathp (cdr p)
		  (next (car p) r)))
    t))

;; The final destination of a path:

(defun final (p r)
  (if (consp p)
      (final (cdr p) (next (car p) r))
    r))

;; The number of times r is crossed to or from r during path p:

(defun visits (p r)
  (if (consp p)
      (if (bridgep (car p) r)
	  (1+ (visits (cdr p) r))
	(visits (cdr p) r))
    0))

;; The number of times a path visits a region s is odd iff s is either the
;; origin or the destination of the path, but not both:

(defthmd parity-visits
  (implies (pathp p r)
	   (iff (oddp (visits p s))
		(and (not (equal r (final p r)))
		     (or (equal s r) (equal s (final p r))))))
  :hints (("Goal" :induct (pathp p r))))

;; There is at least 1 region that is neither the origin nor the destination of p:

(defund non-term-region (p r)
  (car (remove1-equal r (remove1-equal (final p r) (regions)))))

(defthmd non-term-region-non-term
  (let ((s (non-term-region p r)))
    (and (member-equal s (regions))
         (not (equal s r))
	 (not (equal s (final p r)))))
  :hints (("Goal" :in-theory (enable non-term-region))))

;; Each region has access to an odd number of bridges:
	     
(defthmd parity-bridges
  (implies (member-equal r (regions))
	   (oddp (visits (bridges) r))))

(in-theory (disable pathp bridgep regions bridges town (regions) (bridges) (town)))

;; (visits p r) is invariant under permutation of p:

(defthm visits-remove1
  (implies (member-equal x p)
	   (equal (visits (remove1-equal x p) r)
		  (if (bridgep x r)
	              (1- (visits p r))
		    (visits p r)))))

(defthmd permp-visits
  (implies (permutationp p b)
	   (equal (visits p r)
		  (visits b r))))

;; Suppose a path p with origin r crosses every bridge exactly once, i.e, p is a
;; permutation of (bridges). Then (visits p s) is odd for every region s. Consider
;; s = (non-term-region p r).  By parity-visits and non-term-region-non-term,
;; (visits p s) is even, a contradiction.

(defthm konigsberg
  (implies (and (member-equal r (regions))
		(pathp p r))
	   (not (permutationp p (bridges))))
  :hints (("Goal" :use (non-term-region-non-term
                        (:instance permp-visits (b (bridges)) (r (non-term-region p r)))
			(:instance parity-bridges (r (non-term-region p r)))
                        (:instance parity-visits (s (non-term-region p r)))))))


    
