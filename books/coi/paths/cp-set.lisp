; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(in-package "CPATH")

(include-book "../osets/multicons")
(include-book "hints")

(local (in-theory (enable set::weak-insert-induction-helper-1)))
(local (in-theory (enable set::weak-insert-induction-helper-2)))
(local (in-theory (enable set::weak-insert-induction-helper-3)))


;;
;;
;;

(defun cp-set (set st1 st2)
  "Set the value in ST2 of each path P in SET to the value of P in ST1"
  (if (set::empty set) st2
    (let ((p (set::head set)))
      (sp p (gp p st1)
	  (cp-set (set::tail set) st1 st2)))))

(defthmd sp-gp-differential
  (equal (equal r1 r2)
	 (and (equal (gp path r1) (gp path r2))
	      (equal (clrp path r1)
		     (clrp path r2))))
  :hints (("Goal" :use (:instance sp-equal-rewrite-2
				  (r r1)
				  (v (gp path r1))))))

(local
 (defthm clrp-reduction
   (implies
    (equal (gp p st1)
	   (gp p st2))
    (iff (equal (clrp p st1)
		(clrp p st2))
	 (equal st1 st2)))
   :hints (("goal" :use (:instance sp-gp-differential
				   (r1 st1)
				   (r2 st2)
				   (path p))))))

(defthm in-implies-gp-of-cp-set
  (implies
   (set::in path set)
   (equal (gp path (cp-set set st1 x))
	  (gp path st1)))
  :hints (("goal" :in-theory (enable GP-OF-GP gp-of-sp))))

(local
 (defthm gp-domination-implies-equality
   (IMPLIES (AND (EQUAL (GP P1 ST1)
			(GP P1 ST2))
		 (DOMINATES P1 P2))
	    (iff (EQUAL (GP P2 ST1)
			(GP P2 ST2))
		 t))
   :hints (("goal" :in-theory (enable gp dominates))))
 )

(local
 (defthm open-nthcdr
   (implies
    (not (zp n))
    (equal (nthcdr n list)
	   (nthcdr (1- n) (cdr list)))))
 )

(local
 (include-book "arithmetic/top-with-meta" :dir :system)
 )

(local
 (defthm gp-dominates-implies-equality-2
   (implies
    (AND (EQUAL (GP PATH ST1)
		(GP PATH ST2))
	 (DOMINATES P2 PATH)
	 (EQUAL (CLRP (NTHCDR (LEN P2) PATH)
		      (GP P2 ST1))
		(CLRP (NTHCDR (LEN P2) PATH)
		      (GP P2 ST2))))
    (iff (EQUAL (GP P2 ST1)
	       (GP P2 ST2)) t))
   :hints (("goal" :in-theory (enable gp dominates nthcdr))))
 )

(local
 (defthm gp-path-equality-implies-gp-path-cp-set-equality
   (implies
    (equal (gp path st1)
	   (gp path st2))
    (iff (equal (gp path (cp-set set st1 x))
		(gp path (cp-set set st2 x))) t))
   :hints (("goal" :in-theory (enable gp-of-gp gp-of-sp))))
 )

(local
 (defthm clrp-cp-set-reduction
   (implies
    (equal (gp path st1)
	   (gp path st2))
    (iff (equal (clrp path (cp-set set st1 x))
		(clrp path (cp-set set st2 x)))
	 (equal (cp-set set st1 x)
		(cp-set set st2 x))))
   :hints (("goal" :in-theory (e/d (clrp-of-sp
				    sp-equal-rewrite-2)
				   (sp==r)))
	   (and acl2::stable-under-simplificationp
		'(:in-theory (e/d (clrp-of-sp
				   diverge
				   sp-equal-rewrite-2)
				  (sp==r))))))
 )

(defthmd equal-cp-set-reduction-reduction-helper
  (implies
   (set::in p set)
   (iff (equal (cp-set set st1 x)
	       (cp-set set st2 x))
	(and (equal (gp p st1)
		    (gp p st2))
	     (equal (cp-set set st1 x)
		    (cp-set set st2 x)))))
  :hints (("goal" :in-theory (e/d (sp-equal-rewrite-2)
				  (sp==r)))))

(defthmd open-cp-set
  (implies
   (not (set::empty set))
   (equal (cp-set set st1 st2)
	  (LET ((P (SET::HEAD SET)))
	       (SP P (GP P ST1)
		   (CP-SET (SET::TAIL SET) ST1 ST2))))))

(local
 (defthm cp-set-and-gp-equal-implies-cp-set-insert-equal
   (implies
    (and
     (equal (cp-set set st1 x)
	    (cp-set set st2 x))
     (equal (gp p st1)
	    (gp p st2)))
    (iff (equal (cp-set (set::insert p set) st1 x)
		(cp-set (set::insert p set) st2 x)) t))
   :hints (("goal" :in-theory (e/d (open-cp-set sp-equal-rewrite-2)
				   (sp==r)))))
 )

(defun cp-set-equal (set st1 st2)
  (if (set::empty set) t
    (and (equal (gp (set::head set) st1)
		(gp (set::head set) st2))
	 (cp-set-equal (set::tail set) st1 st2))))

(defthmd equal-cp-set-to-cp-set-equal
  (iff (equal (cp-set set st1 x)
	      (cp-set set st2 x))
       (cp-set-equal set st1 st2))
  :hints (("goal" :in-theory (e/d (open-cp-set sp-equal-rewrite-2)
				  (sp==r)))))

(defthm equal-gp-from-cp-set-equal-membership
  (implies
   (and
    (set::in a set)
    (cp-set-equal set st1 st2))
   (iff (equal (gp a st1)
	       (gp a st2)) t))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :corollary
		  (implies
		   (and
		    (set::in a set)
		    (cp-set-equal set st1 st2))
		   (equal (gp a st1) (gp a st2))))))

(defthm cp-set-equal-from-subset
  (implies
   (and
    (cp-set-equal set2 st1 st2)
    (set::subset set1 set2))
   (cp-set-equal set1 st1 st2)))

(local
 (defthm cp-set-insert-equal-implies-cp-set-equal
   (implies
    (equal (cp-set (set::insert a set) st1 x)
	   (cp-set (set::insert a set) st2 x))
    (iff (equal (cp-set set st1 x)
		(cp-set set st2 x)) t))
   :hints (("goal" :in-theory (enable equal-cp-set-to-cp-set-equal))))
 )

;; There is a similar theorem for set::union

(defthm equal-cp-set-insert-reduction
  (iff (equal (cp-set (set::insert p set) st1 x)
	      (cp-set (set::insert p set) st2 x))
       (and (equal (gp p st1)
		   (gp p st2))
	    (equal (cp-set set st1 x)
		   (cp-set set st2 x))))
  :hints (("goal"
	   :in-theory nil
	   :use (:instance equal-cp-set-reduction-reduction-helper
			   (set (set::insert p set))))
	  ("goal'" :cases ((not (set::in p set)))
	   :in-theory (current-theory :here))))

(defthm cp-set-equal-insert-reduction
  (iff (cp-set-equal (set::insert p set) st1 st2)
       (and (equal (gp p st1) (gp p st2))
	    (cp-set-equal set st1 st2)))
  :hints (("goal" :use (:instance equal-cp-set-insert-reduction)
	   :in-theory '(equal-cp-set-to-cp-set-equal))))

(defthm cp-set-equal-union-reduction
  (iff (cp-set-equal (set::union s1 s2) st1 st2)
       (and (cp-set-equal s1 st1 st2)
	    (cp-set-equal s2 st1 st2))))

(defthm equal-cp-set-union-reduction
  (iff (equal (cp-set (set::union s1 s2) st1 x)
	      (cp-set (set::union s1 s2) st2 x))
       (and (equal (cp-set s1 st1 x)
		   (cp-set s1 st2 x))
	    (equal (cp-set s2 st1 x)
		   (cp-set s2 st2 x))))
  :hints (("goal" :use (:instance cp-set-equal-union-reduction)
	   :in-theory '(equal-cp-set-to-cp-set-equal))))

(defmacro gp-set (set st)
  `(cp-set ,set ,st nil))

;;
;; clrp is another important "function" ..
;;

(defthmd cp-set-equal-to-equal-cp-set
  (iff (cp-set-equal set st1 st2)
       (equal (cp-set set st1 nil)
	      (cp-set set st2 nil)))
  :hints (("goal" :in-theory (enable EQUAL-CP-SET-TO-CP-SET-EQUAL))))

(defthm gp-of-gp-domination
  (implies
   (dominates a y)
   (equal (gp (nthcdr (len a) y) (gp a x))
	  (gp y x)))
  :hints (("goal" :in-theory (enable gp-of-gp))))

(defthm outer-domination
  (equal (sp a v (cp-set set (sp a v x1) x2))
	 (sp a v (cp-set set x1 x2)))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
	   :in-theory (e/d (CLRP-COMMUTE-2
			    ;;gp-of-gp
			    gp-of-sp
			    clrp-of-sp
			    sp-equal-rewrite-2)
			   (CLRP-OF-CLRP
			    sp==r)))))

(defthm cp-set-over-sp
  (implies
   (equal v (gp a st1))
   (equal (cp-set set st1 (sp a v st2))
	  (sp a v (cp-set set st1 st2))))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
	   :in-theory (e/d (CLRP-COMMUTE-2
			    ;;gp-of-gp
			    gp-of-sp
			    clrp-of-sp
			    sp-equal-rewrite-2)
			   (CLRP-OF-CLRP
			    sp==r)))))

(defthm cp-set-cp-set
  (equal (cp-set set (cp-set set st1 st2) st3)
	 (cp-set set st1 st3))
  :hints (("goal" :in-theory (disable SP==R))))



(defun clrp-set (set st)
  (if (set::empty set) st
    (clrp-set (set::tail set) (clrp (set::head set) st))))

(defthm open-clrp-set-on-constants
  (implies (syntaxp (quotep set))
           (equal (clrp-set set st)
                  (if (set::empty set)
                      st
                    (clrp-set (set::tail set)
                              (clrp (set::head set) st)))))
  :hints (("Goal" :in-theory (enable clrp-set))))

(defun clrp-set-induction (set r1 r2)
  (if (set::empty set) (cons r1 r2)
    (clrp-set-induction (set::tail set)
			(clrp (set::head set) r1)
			(clrp (set::head set) r2))))

(defthm cp-set-equal-identity
  (cp-set-equal set x x))

(defthm cp-set-equal-dominance
  (implies
   (cp-set-equal set x y)
   (cp-set-equal set (clrp a x) (clrp a y))))

(defthmd record-equal-to-gp-set-equal-helper
  (iff (equal r1 r2)
       (and (cp-set-equal set r1 r2)
	    (equal (clrp-set set r1)
		   (clrp-set set r2))))
  :hints (("goal" :induct (clrp-set-induction set r1 r2))))

(defthmd record-equal-to-gp-set-equal
  (iff (equal r1 r2)
       (and (equal (gp-set set r1)
		   (gp-set set r2))
	    (equal (clrp-set set r1)
		   (clrp-set set r2))))
  :hints (("goal" :use (:instance record-equal-to-gp-set-equal-helper)
	   :in-theory (enable cp-set-equal-to-equal-cp-set))))

;;
;; In support of incremental-cp-set-equality-reduction
;;

(defthmd open-cp-set-equal
  (implies
   (not (set::empty set))
   (equal (cp-set-equal set st1 st2)
	  (AND (EQUAL (GP (SET::HEAD SET) ST1)
		      (GP (SET::HEAD SET) ST2))
	       (CP-SET-EQUAL (SET::TAIL SET)
			     ST1 ST2)))))

(defun keep-exposed-elements (a x)
  (if (set::empty x) (set::emptyset)
    (let ((head (set::head x)))
      (if (dominates a head)
	  (set::insert (list::fix (nthcdr (len a) head))
		       (keep-exposed-elements a (set::tail x)))
	(if (dominates head a)
	    (set::insert nil
			 (keep-exposed-elements a (set::tail x)))
	  (keep-exposed-elements a (set::tail x)))))))

(defthmd incremental-cp-set-equality-reduction-helper-1
  (implies
   (and
    (cp-set-equal (keep-exposed-elements a x) v1 v2)
    (equal (gp a xx1) (gp a xx2)))
   (equal (cp-set-equal x (sp a v1 xx1) (sp a v2 xx2))
	  (cp-set-equal x xx1 xx2)))
  :hints (("goal" :in-theory (e/d (diverge open-clrp-list open-cp-set-equal gp-of-sp)
				  (acl2::equal-booleans-reducton)))))

(include-book "../osets/multiappend")

(defthm multicons-over-insert
  (equal (set::multicons a (set::insert x list))
	 (set::insert (cons a x) (set::multicons a list))))

(defthm multicons-empty
  (implies
   (set::empty x)
   (equal (set::multicons a x) nil))
  :hints (("goal" :expand (set::multicons a x))))

(defthm multiappend-empty
  (implies
   (set::empty x)
   (equal (set::multiappend a x) nil))
  :hints (("goal" :in-theory (enable set::multiappend))))

(defthm open-multiappend-on-insert
  (equal (set::multiappend a (set::insert x list))
	 (set::insert (append a x)
		      (set::multiappend a list)))
  :hints (("goal" :induct (set::multiappend a list)
	   :in-theory (e/d (append set::multiappend)
			    (SET::DOUBLE-CONTAINMENT-expensive)))))

(defthmd cp-set-equal-mapappend-reduction
  (equal (cp-set-equal (set::multiappend a (keep-exposed-elements a x)) s1 s2)
	 (cp-set-equal (keep-exposed-elements a x) (gp a s1) (gp a s2)))
  :hints (("goal" :in-theory (enable set::multiappend))))

(defthmd incremental-cp-set-equality-reduction-helper-2
  (implies
   (and
    (cp-set-equal (set::multiappend a (keep-exposed-elements a x)) st1 st2)
    (equal (gp a xx1)
	   (gp a xx2)))
   (equal (cp-set-equal x
			(sp a (gp a st1) xx1)
			(sp a (gp a st2) xx2))
	  (cp-set-equal x xx1 xx2)))
  :hints (("goal" :in-theory (e/d (cp-set-equal-mapappend-reduction
				   incremental-cp-set-equality-reduction-helper-1)
				  (cp-set-equal)))))

(defthm cp-set-equal-implies-cp-set-equal-keep-exposed
  (implies
   (cp-set-equal x s1 s2)
   (cp-set-equal (set::multiappend a (keep-exposed-elements a x)) s1 s2)))

(defthmd incremental-cp-set-equality-reduction-helper-3
  (implies
   (and
    (cp-set-equal x st1 st2)
    (equal (gp a xx1)
	   (gp a xx2)))
   (equal (cp-set-equal x
			(sp a (gp a st1) xx1)
			(sp a (gp a st2) xx2))
	  (cp-set-equal x xx1 xx2)))
  :hints (("goal" :in-theory (e/d (incremental-cp-set-equality-reduction-helper-2)
				  (cp-set-equal)))))

(defthm incremental-cp-set-equality-reduction
  (implies
   (and
    (equal (cp-set x st1 nil)
	   (cp-set x st2 nil))
    (equal (gp a xx1)
	   (gp a xx2)))
   (iff (equal (cp-set x (sp a (gp a st1) xx1) nil)
	       (cp-set x (sp a (gp a st2) xx2) nil))
	(equal (cp-set x xx1 nil)
	       (cp-set x xx2 nil))))
  :hints (("goal" :in-theory `(equal-cp-set-to-cp-set-equal
			       incremental-cp-set-equality-reduction-helper-3))))

(defthmd cp-set-extensionality
  (implies
   (and
    (equal (cp-set x1 st1 nil)
	   (cp-set x2 st2 nil))
    (equal x1 a1)
    (equal x2 a2))
   (iff (equal (cp-set a1 st1 nil)
	       (cp-set a2 st2 nil)) t)))

;;
;; some additional clrp reasoning
;;

(defun clrp-set-equal (set x y)
  (if (set::empty set) (equal x y)
    (clrp-set-equal (set::tail set)
		    (cpath::clrp (set::head set) x)
		    (cpath::clrp (set::head set) y))))

(defthm clrp-set-equal-of-clrp
  (implies
   (set::in a set)
   (equal (clrp-set-equal set (cpath::clrp a x) (cpath::clrp a y))
	  (clrp-set-equal set x y))))

(defthmd clrp-set-equal-implies-1
  (implies
   (clrp-set-equal set x y)
   (equal (cpath::clrp-set set x)
	  (cpath::clrp-set set y)))
  :hints (("goal" :in-theory (enable cpath::clrp-set))))

(defthmd clrp-set-equal-implies-2
  (implies
   (not (clrp-set-equal set x y))
   (not (equal (cpath::clrp-set set x)
	       (cpath::clrp-set set y))))
  :hints (("goal" :in-theory (enable cpath::clrp-set))))

(defthmd equal-clrp-set-to-clrp-set-equal
  (iff (equal (cpath::clrp-set set x)
	      (cpath::clrp-set set y))
       (clrp-set-equal set x y))
  :hints (("Goal" :in-theory (enable
			      clrp-set-equal-implies-1
			      clrp-set-equal-implies-2
			      ))))

(defthm clrp-set-equal-chaining
  (implies
   (and
    (set::subset set1 set2)
    (clrp-set-equal set1 x y))
   (clrp-set-equal set2 x y))
  :hints (("Goal" :in-theory (enable set::subset))))

(defthm clrp-set-chaining
  (implies
   (and
    (set::subset set1 set2)
    (equal (cpath::clrp-set set1 x)
	   (cpath::clrp-set set1 y)))
   (iff (equal (cpath::clrp-set set2 x)
	       (cpath::clrp-set set2 y)) t))
  :hints (("goal" :in-theory (enable equal-clrp-set-to-clrp-set-equal))))
