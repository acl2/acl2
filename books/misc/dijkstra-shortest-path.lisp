; Copyright (C) 2013, Regents of the University of Texas
; Written by: J Strother Moore and Qiang Zhang
;             Department of Computer Sciences
;             Univesity of Texas at Austin
;             October, 2004
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (certify-book "script")

; A Proof of the Correctness of Dijkstra's Shortest Path Algorithm in
; ACL2

; See the paper ``Dijkstra's Shortest Path Algorithm Verified with ACL2''
; by the authors for a description of this script.

; Historical Notes: The first version of this proof was completed by
; Moore in September, 2003.  See /u/moore/shortest-path/dsp6.lisp.
; That file contained 92 defthms, 35 :hints, about 75 clause
; identifiers like "Goal" and "Subgoal" (some occur in comments), and
; 40 :use hints.  In order to learn ACL2, Zhang was given the task by
; Moore, first, to discover (independently) a proof (given the
; invariant), and, then, to clean it up.

; Zhang finished his first proof in December, 2003, using ACL2 Version
; 2.7.  In October, 2004, he cleaned up the proof, eliminating some of
; his hints.  This file is his second proof script.  In February,
; 2005, the authors wrote the paper above and in doing so renamed some
; of Zhang's functions and theorems.

; The current file contains 39 defuns, 126 defthms, 51 hints, 23 of
; which are :use hints mentioning 31 lemma instances.


(in-package "ACL2")

(defun del (x y)
  (if (endp y) nil
    (if (equal x (car y))
	(cdr y)
      (cons (car y) (del x (cdr y))))))

(defun memp (e x)
  (if (endp x) nil
    (or (equal e (car x))
	(memp e (cdr x)))))

(defun setp (s)
  (cond ((endp s) t)
	((memp (car s) (cdr s)) nil)
	(t (setp (cdr s)))))

(defun my-union (s1 s2)
  (cond ((endp s1) s2)
	((memp (car s1) s2)
	 (my-union (cdr s1) s2))
	(t (cons (car s1)
		 (my-union (cdr s1) s2)))))

(defun my-subsetp (s1 s2)
  (cond ((endp s1) t)
	(t (and (memp (car s1) s2)
		(my-subsetp (cdr s1) s2)))))

(defun infinitep (x) (null x))

(defun lt (x y)
  (cond ((infinitep x) nil)
	((infinitep y) t)
	(t (< x y))))

(defun plus (x y)
  (cond ((or (infinitep x)
	     (infinitep y))
	 nil)
	(t (+ x y))))

(defun edge-listp (lst)
  (cond ((endp lst) (equal lst nil))
	((and (consp (car lst))
	      (rationalp (cdar lst))
	      (<= 0 (cdar lst))
	      (not (assoc (caar lst)
			  (cdr lst))))
	 (edge-listp (cdr lst)))
	(t nil)))

(defun graphp (g)
  (cond ((endp g) (equal g nil))
	((and (consp (car g))
	      (edge-listp (cdar g)))
	 (graphp (cdr g)))
	(t nil)))

(defun cons-set (e s)
  (if (memp e s) s
    (cons e s)))

(defun all-nodes (g)
  (cond ((endp g) nil)
	(t (cons-set (caar g)
		     (my-union (strip-cars (cdar g))
			       (all-nodes (cdr g)))))))

(defun nodep (n g) (memp n (all-nodes g)))

(defun neighbors (n g)
  (strip-cars (cdr (assoc n g))))

(defun pathp-aux (path g)
  (cond ((endp path) nil)
	((endp (cdr path))
	 (nodep (car path) g))
	(t (and (memp (cadr path)
		     (neighbors (car path) g))
		(pathp-aux (cdr path) g)))))

(defun pathp (path g)
  (and (true-listp path)
       (pathp-aux path g)))

(defun edge-len (a b g)
  (cdr (assoc b (cdr (assoc a g)))))

(defun path-len (path g)
  (cond ((endp path) nil)
	((endp (cdr path))
	 (if (nodep (car path) g) 0 nil))
	(t (plus (edge-len (car path) (cadr path) g)
		 (path-len (cdr path) g)))))

(defun path (n pt) (cdr (assoc n pt)))

(defun d (n pt g)
  (path-len (path n pt) g))

(defun choose-next (ts pt g)
  (cond ((endp ts) '(non-node))
	((endp (cdr ts)) (car ts))
	((lt (d (car ts) pt g)
	     (d (choose-next (cdr ts) pt g) pt g))
	 (car ts))
	(t (choose-next (cdr ts) pt g))))

(defun reassign (u v-lst pt g)
  (cond ((endp v-lst) pt)
	(t (let* ((v (car v-lst))
		  (w (edge-len u v g)))
	     (cond ((lt (plus (d u pt g) w)
			(d v pt g))
		    (cons (cons v (append (path u pt) (list v)))
			  (reassign u (cdr v-lst) pt g)))
		   (t (reassign u (cdr v-lst) pt g)))))))

(defun dsp (ts pt g)
  (cond ((endp ts) pt)
	(t (let ((u (choose-next ts pt g)))
	     (dsp (del u ts)
		  (reassign u (neighbors u g) pt g)
		  g)))))

(defun dijkstra-shortest-path (a b g)
  (let ((p (dsp (all-nodes g)
		(list (cons a (list a))) g)))
    (path b p)))

;===================================================================
(defun pathp-from-to (p a b g)
  (and (pathp p g)
       (equal (car p) a)
       (equal (car (last p)) b)))

(defthm pathp-from-to-corollary
  (implies (pathp-from-to p a b g)
           (and (pathp p g)
                (equal (car p) a)
                (equal (car (last p)) b))))

(defun pt-propertyp (a pt g)
  (if (endp pt) t
    (and (or (null (cdar pt))
             (pathp-from-to (cdar pt) a (caar pt) g))
	 (pt-propertyp a (cdr pt) g))))

(defthm pathp-from-to-path-1 ; [Custom]
  (implies (and (pt-propertyp a pt g)
		(path u pt))
	   (pathp-from-to (path u pt) a u g))
  :rule-classes :forward-chaining)

(defthm pathp-from-to-path-2 ; [Custom]
  (implies (and (pt-propertyp a pt g)
		(path u pt))
	   (pathp-from-to (path u pt)
			      a u g)))

(defun lte (n1 n2)
  (not (lt n2 n1)))

(defun shorterp (p1 p2 g)
  (lte (path-len p1 g)
       (path-len p2 g)))

(defun confinedp (p fs)
  (if (endp p) t
    (if (endp (cdr p)) t
      (and (memp (car p) fs)
	   (confinedp (cdr p) fs)))))

(defun-sk shortest-confined-pathp (a b p fs g)
  (forall path (implies (and (pathp-from-to path a b g)
			     (confinedp path fs))
			(shorterp p path g))))


(defun-sk shortest-pathp (a b p g)
  (forall path (implies (pathp-from-to path a b g)
			(shorterp p path g))))

(defun ts-propertyp (a ts fs pt g)
  (if (endp ts) t
    (and (shortest-confined-pathp a (car ts) (path (car ts) pt) fs g)
	 (confinedp (path (car ts) pt) fs)
	 (ts-propertyp a (cdr ts) fs pt g))))

(defun fs-propertyp (a fs fs0 pt g)
  (if (endp fs) t
    (and (shortest-pathp a (car fs) (path (car fs) pt) g)
	 (confinedp (path (car fs) pt) fs0)
	 (fs-propertyp a (cdr fs) fs0 pt g))))

(defun comp-set (ts s)
  (if (endp s) nil
    (if (memp (car s) ts)
	(comp-set ts (cdr s))
      (cons (car s) (comp-set ts (cdr s))))))

(defun invp (ts pt g a)
  (let ((fs (comp-set ts (all-nodes g))))
    (and (ts-propertyp a ts fs pt g)
	 (fs-propertyp a fs fs pt g)
	 (pt-propertyp a pt g))))

(defthm prop-path-nil ; [Custom]
  (ts-propertyp a s nil (list (cons a (list a))) g))

(defthm comp-set-subset
  (implies (my-subsetp s1 s2)
           (not (comp-set s2 s1))))

(defthm subsetp-cons
  (implies (my-subsetp x y)
           (my-subsetp x (cons e y))))

(defthm subsetp-x-x
  (my-subsetp x x))

(defthm comp-set-id
  (equal (comp-set s s) nil))

(defthm invp-0 ; [Custom]
  (implies (nodep a g)
	   (invp (all-nodes g) (list (cons a (list a))) g a)))

;====================================================================
(defthm subset-union
  (implies (or (my-subsetp s1 s2)
               (my-subsetp s1 s3))
           (my-subsetp s1 (my-union s2 s3))))

(defthm memp-subset-memp-temp
  (implies (and (memp a s)
                (my-subsetp s r))
           (memp a r)))

(defthm neighbor-implies-nodep
  (implies (memp v (neighbors u g))
           (memp v (all-nodes g))))

(defthm paths-table-reassign-lemma2
  (implies (and (pathp p g)
                (memp v (neighbors (car (last p)) g)))
           (pathp (append p (list v)) g))
  :hints (("Goal" :in-theory (disable neighbors))))

(defthm car-append
  (implies (and (true-listp p) p)
           (equal (car (append p lst))
                  (car p))))

(defthm last-append
  (equal (car (last (append p (list v))))
         v))

(defthm paths-table-reassign-lemma4 ; [Custom]
  (implies (and (pt-propertyp a pt g)
                (path u pt)
                (graphp g)
                (memp v (neighbors u g)))
           (pathp-from-to (append (path u pt) (list v))
                         a v g))
  :hints (("Goal" :in-theory (disable neighbors))))

(defthm path-len-implies-not-nil
  (implies (path-len (path u pt) g)
           (path u pt)))

(defthm edge-len-implies-neighbors
  (implies (edge-len u v g)
           (memp v (neighbors u g))))

(defthm pt-propertyp-reassign ; [Custom]
  (implies (and (pt-propertyp a pt g)
                (graphp g)
		(my-subsetp v-lst (all-nodes g)))
	   (pt-propertyp a (reassign u v-lst pt g) g))
  :hints (("Goal" :in-theory (disable path edge-len neighbors))))

;=====================================================================
(defthm shortest-pathp-corollary
  (implies (and (shortest-pathp a b p g)
                (pathp-from-to path a b g))
           (shorterp p path g))
  :hints (("Goal" :use shortest-pathp-necc)))

(defthm shortest-implies-unchanged-lemma1 ; [Custom]
  (equal (path v (cons (cons u path) pt))
         (if (equal v u) path
           (path v pt))))

(defthm memp-implies-memp-union-1
    (implies (memp u s1)
             (memp u (my-union s1 s2))))

(defthm memp-implies-memp-union-2
    (implies (memp u s2)
             (memp u (my-union s1 s2))))

(defthm not-memp-edge-len-lemma
  (implies (assoc v alst)
           (memp v (strip-cars alst))))

(defthm not-memp-edge-len
  (implies (not (memp v (all-nodes g)))
           (not (edge-len a v g))))

(defthm path-len-append
  (implies (pathp p g)
           (equal (path-len (append p (list v)) g)
                  (plus (path-len p g)
                        (edge-len (car (last p)) v g))))
  :hints (("Goal" :in-theory (disable neighbors edge-len))))

(defthm pathp-implies-true-listp
  (implies (pathp p g)
           (true-listp p)))

(defthm shortest-implies-unchanged ; [Custom]
  (implies (and (shortest-pathp a v (path v pt) g)
                (pt-propertyp a pt g)
                (graphp g)
                (nodep v g))
           (equal (path v (reassign u v-lst pt g))
                  (path v pt)))
  :hints (("Goal"
           :in-theory (disable path edge-len neighbors pathp
                               shortest-pathp))
          ("Subgoal *1/2"
           :use ((:instance path-len-implies-not-nil)
                                (:instance pathp-from-to-corollary
                                           (p (path u pt)) (b u))
				(:instance shortest-pathp-corollary
                                           (path (append (path u pt) (list v)))
                                           (b v) (p (path v pt)))))))
;=====================================================================
(defthm fs-propertyp-memp ; [Custom]
  (implies (and (fs-propertyp a fs s pt g)
		(memp v fs))
	   (and (shortest-pathp a v (path v pt) g)
		(confinedp (path v pt) s))))

(defthm fs-propertyp-memp-lemma ; [Custom]
  (implies (and (my-subsetp fs (all-nodes g))
		(fs-propertyp a fs s pt g)
		(pt-propertyp a pt g)
                (graphp g)
		(memp v fs))
	   (equal (path v (reassign u (neighbors u g) pt g))
		  (path v pt)))
  :hints (("Goal" :in-theory (disable neighbors path shortest-pathp))))

(defthm fs-propertyp-choose-next-lemma1 ; [Custom]
  (implies (and (fs-propertyp a fs s pt g)
		(pt-propertyp a pt g)
                (graphp g)
		(my-subsetp fs (all-nodes g)))
	   (fs-propertyp a fs s (reassign u (neighbors u g) pt g) g))
  :hints (("Goal" :in-theory (disable neighbors path shortest-pathp))))

(defthm fs-propertyp-choose-lemma2 ; [Custom]
  (implies (and (fs-propertyp a fs s pt g)
		(my-subsetp fs (all-nodes g))
		(confinedp (path u pt) s)
		(pt-propertyp a pt g)
		(nodep u g)
                (graphp g)
		(shortest-pathp a u (path u pt) g))
	   (fs-propertyp a (cons u fs) s
			 (reassign u (neighbors u g) pt g)
			 g))
  :hints (("Goal" :in-theory (disable path neighbors))))

(defthm fs-propertyp-choose-lemma3 ; [Custom]
  (implies (and (my-subsetp s fs)
		(my-subsetp fs (all-nodes g))
		(pt-propertyp a pt g)
		(fs-propertyp a fs ss pt g))
	   (fs-propertyp a s ss pt g))
  :hints (("Goal" :in-theory (disable shortest-pathp path))))

(defthm fs-propertyp-choose-lemma4-lemma ; [Custom]
  (implies (and (my-subsetp s ss)
		(confinedp p s))
	   (confinedp p ss)))

(defthm fs-propertyp-choose-lemma4 ; [Custom]
  (implies (and (my-subsetp s ss)
		(fs-propertyp a fs s pt g))
	   (fs-propertyp a fs ss pt g)))

(defun find-partial-path (p s)
  (if (endp p) nil
    (if (memp (car p) s)
	(cons (car p) (find-partial-path (cdr p) s))
      (list (car p)))))

(defthm edge-listp-values-positive
  (implies (and (edge-listp a)
                (cdr (assoc-equal b a)))
           (<= 0 (cdr (assoc-equal b a))))
  :rule-classes :linear)

(defthm graph-weight-nonneg
  (implies (and (graphp g)
		(edge-len a b g))
	   (<= 0 (edge-len a b g)))
  :rule-classes :linear)

(defthm graph-path-weight-nonneg
  (implies (and (graphp g)
		(path-len p g))
	   (<= 0 (path-len p g)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable edge-len))))

(defthm edge-len-implies-nodep
  (implies (edge-len a b g)
           (memp a (all-nodes g))))

(defthm partial-path-shorterp
  (implies (graphp g)
	   (shorterp (find-partial-path p s)
			 p g))
  :hints (("Goal" :induct (find-partial-path p s)
           :in-theory (disable edge-len))))

(defthm notnodep-necc
  (implies (not (nodep a g))
	   (not (neighbors a g))))

(defthm pathp-implies-car-nodep
  (implies (pathp p g)
           (memp (car p) (all-nodes g))))

(defthm pathp-partial-path
  (implies (pathp p g)
           (and (pathp-from-to (find-partial-path p s) (car p)
                              (car (last (find-partial-path p s))) g)
                (confinedp (find-partial-path p s) s))))

(defthm shorterp-trans
  (implies (and (shorterp p1 p2 g)
                (shorterp p2 p3 g))
           (shorterp p1 p3 g)))

(defthm shorterp-by-partial-trans
  (implies (and (shorterp p (find-partial-path path s) g)
                (graphp g))
           (shorterp p path g))
  :hints (("Goal" :in-theory (disable shorterp))))

(defthm ts-propertyp-prop-lemma1 ; [Custom]
  (implies (and (ts-propertyp a ts fs pt g)
		(memp v ts))
	   (and (shortest-confined-pathp a v (path v pt) fs g)
		(confinedp (path v pt) fs)))
  :rule-classes ((:rewrite)(:forward-chaining)))

(defthm ts-propertyp-prop-lemma2 ; [Custom]
  (implies (and (pathp-from-to path a b g)
                (shortest-confined-pathp a b p fs g)
                (confinedp path fs))
	   (shorterp p path g))
  :hints (("Goal" :use shortest-confined-pathp-necc)))

(defthm ts-propertyp-prop ; [Custom]
  (implies (and (ts-propertyp a ts fs pt g)
		(confinedp path fs)
		(pathp-from-to path a v g)
		(memp v ts))
	   (and (shorterp (path v pt) path g)
		(confinedp (path v pt) fs)))
  :hints (("Goal" :in-theory (disable path shorterp pathp-from-to))))

(defthm shorterp-by-partial-and-choose-next ; [Custom]
  (implies (and (shorterp (path u pt) (path v pt) g)
		(memp v ts)
		(ts-propertyp a ts (comp-set ts (all-nodes g)) pt g)
		(pathp-from-to path a v g)
		(confinedp path (comp-set ts (all-nodes g))))
	   (shorterp (path u pt) path g))
  :hints (("Goal" :in-theory (disable path shorterp))))

(defthm choose-next-shorterp-other ; [Custom]
  (implies (memp v ts)
           (shorterp (path (choose-next ts pt g) pt)
                    (path v pt) g)))

(defthm not-comp-set-id
  (implies (memp v all)
           (iff (memp v (comp-set ts all))
                (not (memp v ts)))))

(defthm find-partial-path-last-memp
  (implies (and (memp (car (last p)) ts)
		(pathp p g)
		(my-subsetp ts (all-nodes g)))
	   (memp (car (last (find-partial-path p (comp-set ts (all-nodes g)))))
		ts)))

(defthm choose-next-shortest-lemma ; [Custom]
  (implies (consp ts)
	   (memp (choose-next ts pt g) ts)))

(defthm choose-next-shortest ; [Custom]
  (implies (and (graphp g)
		(consp ts)
		(my-subsetp ts (all-nodes g))
		(invp ts pt g a))
	   (shortest-pathp a (choose-next ts pt g)
                           (path (choose-next ts pt g) pt) g))
  :hints
  (("Goal" :in-theory (disable shorterp path pathp)
    :use ((:instance
           pathp-partial-path
           (p (shortest-pathp-witness a (choose-next ts pt g)
                                      (path (choose-next ts pt g) pt)
                                      g))
           (s (comp-set ts (all-nodes g))))
          (:instance
           shorterp-by-partial-and-choose-next
           (u (choose-next ts pt g))
           (path (find-partial-path
                  (shortest-pathp-witness a
                                          (choose-next ts pt g)
                                          (path (choose-next ts pt g) pt)
                                          g)
                  (comp-set ts (all-nodes g))))
           (v (car (last (find-partial-path
                          (shortest-pathp-witness a (choose-next ts pt g)
                                                  (path (choose-next ts pt g)
                                                        pt)
                                                  g)
                          (comp-set ts (all-nodes g)))))))))))

(defthm choose-next-confinedp ; [Custom]
  (implies (and (invp ts pt g a)
		(consp ts)
		(my-subsetp ts (all-nodes g)))
	   (confinedp (path (choose-next ts pt g) pt)
			      (comp-set ts (all-nodes g))))
  :hints (("Goal" :in-theory (disable path))))

(defthm subsetp-comp-set-all
  (my-subsetp (comp-set ts all) all))

(defthm subsetp-del
  (my-subsetp (del u ts) ts))

(defthm cons-subsetp-comp-set-del-lemma
  (my-subsetp (comp-set ts all)
	      (comp-set (del u ts) all)))

(defthm subsetp-comp-set-del-lemma1
  (implies (my-subsetp s1 (cons v s2))
	   (my-subsetp s1
		       (list* v u s2))))

(defthm subsetp-comp-set-del-lemma2
  (implies (and (memp v ts)
                (not (equal v u)))
           (memp v (del u ts))))

(defthm subsetp-comp-set-del
  (implies (and (setp ts)
		(setp all))
	   (my-subsetp (comp-set (del u ts) all)
		       (cons u (comp-set ts all)))))

(defthm edge-listp-prop
  (implies (and (edge-listp lst)
		(not (assoc u lst)))
	   (not (memp u (strip-cars lst)))))

(defthm edge-listp-implies-setp
  (implies (edge-listp lst)
	   (setp (strip-cars lst))))

(defthm not-memp-union
  (implies (and (not (memp u s1))
		(not (memp u s2)))
	   (not (memp u (my-union s1 s2)))))

(defthm setp-union
  (implies (and (setp s1)
		(setp s2))
	   (setp (my-union s1 s2))))

(defthm setp-all-nodes
  (implies (graphp g)
           (setp (all-nodes g))))

(defthm memp-subset-memp
  (implies (and (my-subsetp s r)
                (memp a s))
           (memp a r)))

(defthm neighbors-subsetp-all-nodes
  (my-subsetp (neighbors u g)
              (all-nodes g)))

(defthm fs-propertyp-choose ; [Custom]
  (implies (and (invp ts pt g a)
		(my-subsetp ts (all-nodes g))
		(graphp g)
		(consp ts)
		(setp ts))
	   (let ((u (choose-next ts pt g)))
	     (fs-propertyp a (comp-set (del u ts)
				       (all-nodes g))
			   (comp-set (del u ts) (all-nodes g))
			   (reassign u (neighbors u g) pt g)
			   g)))
  :hints (("Goal" :in-theory (disable fs-propertyp-choose-lemma3
				      fs-propertyp-choose-lemma4
				      path neighbors shortest-pathp
				      fs-propertyp)
	   :use ((:instance fs-propertyp-choose-lemma4
			    (fs (comp-set (del (choose-next ts pt g) ts)
					  (all-nodes g)))
			    (s (comp-set ts (all-nodes g)))
			    (ss (comp-set (del (choose-next ts pt g) ts)
					  (all-nodes g)))
			    (pt (reassign (choose-next ts pt g)
					  (neighbors (choose-next ts pt g) g)
					  pt g)))
		 (:instance fs-propertyp-choose-lemma3
			    (s (comp-set (del (choose-next ts pt g) ts)
					  (all-nodes g)))
			    (fs (cons (choose-next ts pt g)
				      (comp-set ts (all-nodes g))))
			    (ss (comp-set ts (all-nodes g)))
			    (pt (reassign (choose-next ts pt g)
					  (neighbors (choose-next ts pt g) g)
					  pt g)))))))
;=====================================================================
(defthm neighbor-implies-edge-len
  (implies (and (graphp g)
                (memp v (neighbors u g)))
           (edge-len u v g)))

(defthm pathp-implies-path-len
  (implies (and (graphp g)
		(pathp p g))
		(path-len p g))
  :hints (("Goal" :in-theory (disable neighbors edge-len))))

(defthm path-pt-iff-path-len ; [Custom]
  (implies (and (graphp g)
                (pt-propertyp a pt g))
           (iff (path u pt)
                (path-len (path u pt) g))))

(defthm reassign-path ; [Custom]
  (implies (not (memp v v-lst))
	   (equal (path v (reassign u v-lst pt g))
		  (path v pt))))

(defthm shorterp-reassign-append ; [Custom]
  (implies (and (pt-propertyp a pt g)
                (graphp g)
                (path u pt)
                (memp v v-lst))
           (shorterp (path v (reassign u v-lst pt g))
                    (append (path u pt) (list v)) g))
  :hints (("Goal" :in-theory (disable edge-len path pathp-from-to-path-1))
          ("Subgoal *1/3"
           :use ((:instance pathp-from-to-corollary
                            (p (path u pt)) (b u))))))

(defun find-last-next-path (p)
  (if (or (endp p) (endp (cdr p))) nil
    (cons (car p) (find-last-next-path (cdr p)))))

(defun last-node (p)
  (car (last (find-last-next-path p))))

(defthm shorterp-reassign-lemma ; [Custom]
  (implies (and (path-len (path u pt) g)
                (pt-propertyp a pt g))
           (and (pathp (path u pt) g)
                (equal (car (path u pt)) a)
                (equal (car (last (path u pt))) u))))

(defthm shorterp-reassign ; [Custom]
  (implies (pt-propertyp a pt g)
           (shorterp (path v (reassign u v-lst pt g))
                    (path v pt) g))
  :hints (("Goal" :in-theory (disable path edge-len neighbors))))

(defthm true-listp-path ; [Custom]
  (implies (pt-propertyp a pt g)
	   (true-listp (path u pt))))

(defthm pathp-from-to-append ; [Custom]
  (implies (and (pt-propertyp a pt g)
		(path w pt)
		(memp v (neighbors w g)))
	   (pathp-from-to (append (path w pt)
				 (list v))
			 a v g))
  :hints (("Goal" :in-theory (disable neighbors path))))

(defthm confinedp-append
  (implies (and (confinedp p s)
		(memp (car (last p)) s))
	   (confinedp (append p (list v)) s)))

(defthm shorterp-than-append-fs ; [Custom]
  (implies (and (shortest-confined-pathp a v (path v pt) s g)
		(fs-propertyp a fs s pt g)
		(my-subsetp fs s)
		(path w pt)
		(pt-propertyp a pt g)
		(memp w fs))
	   (shorterp (path v pt)
		    (append (path w pt) (list v)) g))
  :rule-classes nil
  :hints (("Goal" :use ((:instance ts-propertyp-prop-lemma2
                                   (b v) (p (path v pt)) (fs s)
                                   (path (append (path w pt) (list v)))))
           :in-theory (disable path shortest-confined-pathp pathp))))

(defthm path-length
  (implies (and (pathp p g)
                (not (equal (car p)
                            (car (last p)))))
           (<= 2 (len p)))
  :rule-classes :linear)

(defthm pathp-find-last-next
  (implies (and (pathp p g)
		(<= 2 (len p)))
	   (and (pathp (find-last-next-path p) g)
		(memp (car (last p))
		     (neighbors (car (last (find-last-next-path p))) g))))
  :hints (("Goal" :in-theory (disable neighbors))))

(defthm find-last-implies-all-in
  (implies (and (find-last-next-path p)
		(confinedp p fs))
	   (memp (car (last (find-last-next-path p))) fs)))

(defthm pathp-from-to-implies-all-path
  (implies (and (pathp-from-to p a v g)
		(not (equal a v))
		(confinedp p fs))
	   (and (memp v (neighbors (last-node p) g))
                (pathp-from-to (find-last-next-path p) a (last-node p) g)
		(memp (last-node p) fs)))
  :hints (("Goal" :in-theory (disable pathp neighbors))))

(defthm path-len-implies-pathp
  (implies (and (path-len p g)
                (true-listp p))
           (pathp p g))
  :hints (("Goal" :in-theory (disable edge-len neighbors))))

(defthm shorterp-and-pathp-implies-pathp
  (implies (and (graphp g)
		(shorterp p1 p2 g)
		(true-listp p1)
		(pathp p2 g))
	   (pathp p1 g))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable pathp))))

(defthm shorterp-implies-append-shorterp
  (implies (and (shorterp p1 p2 g)
		(graphp g)
		(true-listp p1)
		(equal (car (last p1))
		       (car (last p2)))
		(pathp p2 g))
	   (shorterp (append p1 (list v))
		    (append p2 (list v)) g))
  :hints (("Goal" :use shorterp-and-pathp-implies-pathp)))

(defthm path-pt-implies-path-last-node ; [Custom]
  (implies (and (pt-propertyp a pt g)
		(pathp (path u pt) g))
	   (equal (car (last (path u pt))) u)))

(defthm last-node-lemma1 ; [Custom]
  (implies (and (graphp g)
		(pt-propertyp a pt g)
		(pathp-from-to p a v g)
		(not (equal a v))
		(shortest-pathp a (last-node p) (path (last-node p) pt) g))
	   (shorterp (append (path (last-node p) pt) (list v))
		    (append (find-last-next-path p) (list v)) g))
  :hints (("Goal" :in-theory (disable shortest-pathp shorterp path pathp)
	   :use ((:instance shorterp-and-pathp-implies-pathp
                            (p1 (path (car (last (find-last-next-path p))) pt))
                            (p2 (find-last-next-path p)))
                 (:instance shortest-pathp-corollary
                            (b (car (last (find-last-next-path p))))
                            (p (path (car (last (find-last-next-path p))) pt))
                            (path (find-last-next-path p)))))))

(defthm last-node-lemma2 ; [Custom]
  (implies (and (equal (car (last p)) v)
		(pathp p g))
	   (equal (append (find-last-next-path p) (list v))
		  p)))

(defthm last-node-lemma ; [Custom]
  (implies (and (graphp g)
		(pt-propertyp a pt g)
		(pathp-from-to p a v g)
		(not (equal a v))
		(shortest-pathp a (last-node p) (path (last-node p) pt) g))
	   (shorterp (append (path (last-node p) pt) (list v))
		    p g))
  :hints (("Goal" :use ((:instance last-node-lemma1)
			(:instance last-node-lemma2))
	   :in-theory (disable shorterp))))

(defthm memp-not-car-implies-memp
  (implies (and (memp v (cons u fs))
		(not (equal v u)))
	   (memp v fs)))

(defthm fs-propertyp-implies-pathp ; [Custom]
  (implies (and (graphp g)
		(fs-propertyp a fs s pt g)
		(memp w fs)
		(pathp-from-to p2 a w g))
	   (path w pt))
  :hints (("Goal" :in-theory (disable path fs-propertyp-memp shortest-pathp
                                      pathp-from-to)
	   :use ((:instance shortest-pathp-corollary
			    (b w) (p (path w pt))
			    (path p2))
		 (:instance fs-propertyp-memp
			    (v w)))))
  :rule-classes nil)

(defthm ts-propertyp-lemma2-1 ; [Custom]
  (implies (and (shortest-confined-pathp a v (path v pt) fs g)
		(graphp g)
		(fs-propertyp a fs fs pt g)
		(pathp-from-to p a v g)
		(not (equal a v))
		(path u pt)
		(shortest-pathp a u (path u pt) g)
		(confinedp p (cons u fs))
		(pt-propertyp a pt g))
	   (shorterp (path v (reassign u (neighbors u g) pt g)) p g))
  :hints (("Goal"
	   :cases ((equal (last-node p) u)))
	  ("Subgoal 2" :in-theory (disable path neighbors shortest-confined-pathp
					   shorterp shortest-pathp memp-not-car-implies-memp
					   fs-propertyp-memp pathp-from-to last-node)
	   :use ((:instance shorterp-trans
			    (p1 (path v (reassign u (neighbors u g) pt g)))
			    (p2 (path v pt))
			    (p3 (append (path (last-node p) pt) (list v))))
                 (:instance shorterp-trans
			    (p1 (path v (reassign u (neighbors u g) pt g)))
			    (p2 (append (path (last-node p) pt) (list v)))
			    (p3 p))
		 (:instance fs-propertyp-memp
			    (s fs)
			    (v (last-node p)))
		 (:instance memp-not-car-implies-memp
			    (v (last-node p)))
		 (:instance fs-propertyp-implies-pathp
			    (s fs)
			    (w (last-node p))
			    (p2 (find-last-next-path p)))
		 (:instance shorterp-than-append-fs
			    (s fs) (w (last-node p)))))
	  ("Subgoal 1" :in-theory (disable path neighbors shortest-confined-pathp
					   last-node shorterp shortest-pathp pathp-from-to)
	   :use ((:instance shorterp-trans
			    (p1 (path v (reassign u (neighbors u g) pt g)))
			    (p2 (append (path u pt) (list v)))
			    (p3 p))))))
;=====================================================================
(defun find-partial-path-to-u (p u)
  (cond ((not (memp u p)) nil)
	((equal (car p) u) (list u))
	(t (cons (car p)
		 (find-partial-path-to-u (cdr p) u)))))

(defthm pathp-implies-path-to-u-pathp
  (implies (and (memp u p)
		(pathp p g))
	   (pathp-from-to (find-partial-path-to-u p u) (car p) u g)))

(defthm not-memp-implies-confinedp
  (implies (and (confinedp p (cons u fs))
		(not (memp u p)))
	   (confinedp p fs)))

(defthm nil-shorterp-than-nil
  (implies (and (shorterp p1 p2 g)
		(graphp g)
		(not p1))
	   (not (pathp p2 g))))

(defthm shortest-pathp-nil-implies-lemma
  (implies (and (shortest-pathp a u p1 g)
		(not p1)
		(graphp g)
		(equal (car p2) a)
		(pathp p2 g))
	   (not (memp u p2)))
  :hints (("Goal" :in-theory (disable pathp shorterp shortest-pathp pathp-implies-path-to-u-pathp)
	   :use ((:instance pathp-implies-path-to-u-pathp
		           (p p2))
		 (:instance nil-shorterp-than-nil
			    (p2 (find-partial-path-to-u p2 u)))))))

(defthm ts-propertyp-lemma2-2 ; [Custom]
  (implies (and (shortest-confined-pathp a v (path v pt) fs g)
		(graphp g)
		(fs-propertyp a fs fs pt g)
		(pathp-from-to p a v g)
		(not (equal a v))
		(shortest-pathp a u (path u pt) g)
		(confinedp p (cons u fs))
		(pt-propertyp a pt g))
	   (shorterp (path v (reassign u (neighbors u g) pt g)) p g))
  :rule-classes nil
  :hints (("Goal" :cases ((path u pt)))
	  ("Subgoal 2" :in-theory (disable neighbors path pathp
                                           pathp-from-to
                                           path-pt-iff-path-len
					   shortest-pathp shorterp
					   shortest-confined-pathp)
	   :use ((:instance shorterp-trans
                            (p1 (path v (reassign u (neighbors u g) pt g)))
                            (p2 (path v pt))
                            (p3 p))
                 (:instance ts-propertyp-prop-lemma2
			    (b v) (p (path v pt))
			    (path p))))
	  ("Subgoal 1" :use ts-propertyp-lemma2-1)))

(defthm shortest-pathp-list-a
  (implies (graphp g)
           (shortest-pathp a a (list a) g)))

(defthm path-a-pt ; [Custom]
  (implies (and (pt-propertyp a pt g)
		(graphp g)
		(nodep a g)
		(equal (path a pt) (list a)))
	   (equal (path a (reassign u v-lst pt g))
		  (path a pt)))
  :hints (("Goal" :use ((:instance shortest-implies-unchanged
                                   (v a))))))

(defthm ts-propertyp-lemma2-3 ; [Custom]
  (implies (and (shortest-confined-pathp a v (path v pt) fs g)
		(graphp g)
		(fs-propertyp a fs fs pt g)
		(nodep a g)
		(pathp-from-to p a v g)
		(confinedp p (cons u fs))
		(shortest-pathp a u (path u pt) g)
		(pt-propertyp a pt g)
		(equal (path a pt) (list a)))
	   (shorterp (path v (reassign u (neighbors u g) pt g)) p g))
  :rule-classes nil
  :hints (("Goal" :cases ((equal a v)))
	  ("Subgoal 2" :use ts-propertyp-lemma2-2)
	  ("Subgoal 1" :in-theory (disable path neighbors pathp
					   shortest-pathp
					   shortest-confined-pathp))))

(defthm ts-propertyp-lemma2 ; [Custom]
  (implies (and (shortest-confined-pathp a v (path v pt) fs g)
		(graphp g)
		(nodep a g)
		(equal (path a pt) (list a))
		(fs-propertyp a fs fs pt g)
		(shortest-pathp a u (path u pt) g)
		(pt-propertyp a pt g))
	   (shortest-confined-pathp a v (path v (reassign u (neighbors u g)
							 pt g))
				   (cons u fs) g))
  :hints (("Goal" :in-theory (disable reassign path neighbors shortest-pathp shortest-confined-pathp)
	   :expand ((shortest-confined-pathp a v (path v (reassign u (neighbors u g)
							 pt g))
					    (cons u fs) g))
	   :use ((:instance ts-propertyp-lemma2-3
			   (p (SHORTEST-CONFINED-PATHP-WITNESS A V
                                   (PATH V (REASSIGN U (NEIGHBORS U G) PT G))
                                   (CONS U FS)
                                   G)))))))

(defthm ts-propertyp-lemma3-1
  (implies (confinedp p fs)
	   (confinedp p (cons u fs))))

(defthm ts-propertyp-lemma3-2 ; [Custom]
  (implies (and (pt-propertyp a pt g)
                (confinedp (path u pt) fs))
	   (confinedp (append (path u pt) (list v))
			      (cons u fs))))

(defthm ts-propertyp-lemma3-3 ; [Custom]
  (implies (and (pt-propertyp a pt g)
                (confinedp (path v pt) fs)
                (confinedp (path u pt) fs))
	   (confinedp (path v (reassign u v-lst pt g))
			      (cons u fs)))
  :hints (("Goal" :in-theory (disable path))))

(defthm ts-propertyp-prop-lemma ; [Custom]
  (implies (and (ts-propertyp a ts fs pt g)
		(memp u ts))
	   (confinedp (path u pt) fs)))

(defthm ts-propertyp-lemma3 ; [Custom]
  (implies (and (pt-propertyp a pt g)
		(graphp g)
		(nodep a g)
		(equal (path a pt) (list a))
		(fs-propertyp a fs fs pt g)
		(ts-propertyp a ts fs pt g)
		(memp u ts)
		(shortest-pathp a u (path u pt) g))
	   (ts-propertyp a (del u ts) (cons u fs)
			 (reassign u (neighbors u g) pt g) g))
  :hints (("Goal" :in-theory (disable path neighbors nodep shortest-pathp
				      shortest-confined-pathp))
	  ("Subgoal *1/2'''" :induct (TS-PROPERTYP A TS2 (CONS TS1 FS)
						 (REASSIGN TS1 (NEIGHBORS TS1 G) PT G)
						 G))))
(defthm shortest-confined-pathp-subset
  (implies (and (shortest-confined-pathp a u p fs g)
                (my-subsetp s fs))
	   (shortest-confined-pathp a u p s g))
  :hints (("Goal" :in-theory (disable shortest-confined-pathp shorterp)
	   :expand ((shortest-confined-pathp a u p s g))
	   :use ((:instance ts-propertyp-prop-lemma2
			    (b u)
			    (path (shortest-confined-pathp-witness a u p s g)))))))

(defthm ts-propertyp-lemma1 ; [Custom]
  (implies (and (my-subsetp s fs)
		(my-subsetp fs s)
                (ts-propertyp a ts fs pt g))
	   (ts-propertyp a ts s pt g))
  :hints (("Goal" :in-theory (disable shortest-confined-pathp))))

(defthm not-memp-del
  (implies (setp ts)
	   (not (memp u (del u ts)))))

(defthm ts-propertyp-choose-next ; [Custom]
  (implies (and (invp ts pt g a)
		(my-subsetp ts (all-nodes g))
		(setp ts)
		(consp ts)
		(graphp g)
		(nodep a g)
		(equal (path a pt) (list a)))
	   (let ((u (choose-next ts pt g)))
	     (ts-propertyp a (del u ts) (comp-set (del u ts) (all-nodes g))
			   (reassign u (neighbors u g) pt g) g)))
  :hints (("Goal" :in-theory (disable neighbors path shortest-pathp)
	   :use ((:instance ts-propertyp-lemma1
			    (pt (reassign (choose-next ts pt g)
					  (neighbors (choose-next ts pt g) g)
					  pt g))
			    (ts (del (choose-next ts pt g) ts))
			    (s (comp-set (del (choose-next ts pt g) ts) (all-nodes g)))
			    (fs (cons (choose-next ts pt g)
				      (comp-set ts (all-nodes g)))))))))

(defthm invp-choose-next ; [Custom]
  (implies (and (invp ts pt g a)
		(my-subsetp ts (all-nodes g))
		(graphp g)
		(consp ts)
		(setp ts)
		(nodep a g)
		(equal (path a pt) (list a)))
	   (let ((u (choose-next ts pt g)))
	     (invp (del u ts)
		  (reassign u (neighbors u g) pt g)
		  g a)))
  :hints (("Goal" :in-theory (disable neighbors))))

(defthm del-subsetp
  (implies (my-subsetp ts s)
	   (my-subsetp (del u ts) s)))

(defthm del-true-listp
  (implies (true-listp ts)
	   (true-listp (del u ts))))

(defthm del-noduplicates
  (implies (setp ts)
	   (setp (del u ts))))

(defthm path-a-pt-reassign ; [Custom]
  (implies (and (pt-propertyp a pt g)
		(graphp g)
		(nodep a g)
		(equal (path a pt) (list a)))
	   (equal (path a (reassign u v-lst pt g))
		  (list a)))
  :hints (("Goal" :in-theory (disable path))))

(defthm invp-last-lemma ; [Custom]
  (implies (and (invp ts pt g a)
		(my-subsetp ts (all-nodes g))
		(nodep a g)
		(equal (path a pt) (list a))
		(true-listp ts)
		(graphp g)
		(setp ts))
	   (invp nil (dsp ts pt g) g a))
  :hints (("Goal" :in-theory (disable path neighbors))))

(defthm true-listp-union
  (implies (and (true-listp lst1)
		(true-listp lst2))
	   (true-listp (my-union lst1 lst2))))

(defthm true-list-all-nodes
  (true-listp (all-nodes g)))

(defthm invp-last ; [Custom]
  (implies (and (nodep a g)
		(graphp g))
	   (invp nil (dsp (all-nodes g)
			 (list (cons a (list a)))
			 g) g a)))

(defthm main-lemma1 ; [Custom]
  (implies (and (invp nil pt g a)
		(nodep b g))
	   (shortest-pathp a b (path b pt) g))
  :hints (("Goal" :in-theory (disable path shortest-pathp))))

(defthm main-lemma2 ; [Custom]
  (implies (and (invp nil pt g a)
		(nodep b g))
	   (or (null (path b pt))
	       (pathp-from-to (path b pt) a b g)))
  :hints (("Goal" :in-theory (disable path)))
  :rule-classes nil)

(defthm main-lemma3 ; [Custom]
  (implies (and (nodep a g)
		(nodep b g)
		(graphp g))
	   (or (null (dijkstra-shortest-path a b g))
	       (pathp-from-to (dijkstra-shortest-path a b g)
			     a b g)))
  :hints (("Goal" :use ((:instance main-lemma2
				   (pt (DSP (ALL-NODES G)
					    (LIST (LIST A A))
					    G))))))
  :rule-classes nil)

(defthm main-lemma4 ; [Custom]
  (implies (and (nodep a g)
		(nodep b g)
		(graphp g))
	   (shortest-pathp a b (dijkstra-shortest-path a b g) g))
  :hints (("Goal" :in-theory (disable shortest-pathp path))))

(defthm main-theorem ; [Custom]
  (implies (and (nodep a g)
		(nodep b g)
		(graphp g))
	   (let ((rho (dijkstra-shortest-path a b g)))
             (and (or (null rho)
                      (pathp-from-to rho a b g))
                  (shortest-pathp a b rho g))))
  :rule-classes nil
  :hints (("Goal" :use (main-lemma3 main-lemma4))))

