;  Copyright (C) 2000 Panagiotis Manolios

;  This program is free software; you can redistribute it and/or modify
;  it under the terms of the GNU General Public License as published by
;  the Free Software Foundation; either version 2 of the License, or
;  (at your option) any later version.

;  This program is distributed in the hope that it will be useful,
;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;  GNU General Public License for more details.

;  You should have received a copy of the GNU General Public License
;  along with this program; if not, write to the Free Software
;  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;  Written by Panagiotis Manolios who can be reached as follows.

;  Email: pete@cs.utexas.edu

;  Postal Mail:
;  Department of Computer Science
;  The University of Texas at Austin
;  Austin, TX 78701 USA

(in-package "ACL2")
#|

This is a set of macros for relating an abstract system and a concrete
system with a WEB.  The systems are non-deterministic.

|#

(defun bor-macro (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (if (consp (cdr lst))
	  (list 'if
		(car lst)
		t
		(bor-macro (cdr lst)))
	(car lst))
    nil))

(defmacro bor (&rest args)
  (bor-macro args))

; The reason for the bor macro is that (or a b) gets expanded to (if a
; a b).  This results in extra rewriting in many situations.  bor is
; equivalent to or if all the arguments are booleans.


; Generate-Full-System is given abs-step, the function that steps the
; abstract system for one step, abs-p, the predicate that recognizes
; abstract states, con-step, the function that steps the concrete
; system for one step, con-p, the predicate that recognizes concrete
; states, and con-rank, the rank of a concrete state.  Note that I am
; assuming that the step of abstract and concrete states depends only
; on the state.  There may be situations in which this is not the
; case.  If so, these macros will have to be altered somewhat.  Also,
; I am assuming that the rank of abstract states is 0.  This may also
; not be the case in general.  R, B, and rank should be undefined.

(defmacro generate-full-system (abs-step abs-p con-step con-p
				con-to-abs good-con con-rank)
  `(progn

     (defun WF-rel (x y)
       (declare (xargs :normalize nil))
       (and (,abs-p x)
	    (,con-p y)
	    (,good-con y)
	    (equal x (,con-to-abs y))))

     (defun B (x y)
       (declare (xargs :normalize nil))
       (bor (WF-rel x y)
	    (WF-rel y x)
	    (equal x y)
	    (and (,con-p x)
		 (,con-p y)
		 (,good-con x)
		 (,good-con y)
		 (equal (,con-to-abs x)
			(,con-to-abs y)))))

     (defun rank (x)
       (declare (xargs :normalize nil))
       (if (,con-p x)
	   (,con-rank x)
	 0))

     (defun R-int (x y int)
       (declare (xargs :normalize nil))
       (cond ((,abs-p x)
	      (equal y (,abs-step x int)))
	     (t (equal y (,con-step x int)))))

     (defun-sk R (x y)
       (exists (int)
	 (r-int x y int)))

     (encapsulate
      ()
      (local (in-theory nil))

      (defthm WF-rel-fc
	(equal (Wf-rel x y)
	       (and (,abs-p x)
		    (,con-p y)
		    (,good-con y)
		    (equal x (,con-to-abs y))))
	:hints (("goal" :by Wf-rel))
	:rule-classes ((:forward-chaining :trigger-terms ((Wf-rel x y)))))

      (defthm B-fc
	(equal (B x y)
	       (bor (WF-rel x y)
		    (WF-rel y x)
		    (equal x y)
		    (and (,con-p x)
			 (,con-p y)
			 (,good-con x)
			 (,good-con y)
			 (equal (,con-to-abs x)
				(,con-to-abs y)))))
	:hints (("goal" :by B))
	:rule-classes ((:forward-chaining :trigger-terms ((B x y)))))

      (defthm rank-fc
	(equal (rank x)
	       (if (,con-p x)
		   (,con-rank x)
		 0))
	:hints (("goal" :by rank))
	:rule-classes ((:forward-chaining :trigger-terms ((rank x)))))

      (defthm R-int-fc
	(equal (R-int x y int)
	       (cond ((,abs-p x)
		      (equal y (,abs-step x int)))
		     (t (equal y (,con-step x int)))))
	:hints (("goal" :by R-int))
	:rule-classes ((:forward-chaining :trigger-terms ((R-int x y int)))))

      (defthm R-fc
	(equal (R x y)
	       (R-int x y (R-witness x y)))
	:hints (("goal" :use R))
	:rule-classes
	((:forward-chaining :trigger-terms ((R x y)))))

      )
     )
  )

(defmacro prove-web (abs-step abs-p con-step con-p con-to-abs con-rank)
  `(progn
     (defthm B-is-a-WF-bisim-core
       (let ((u (,abs-step s int))
	     (v (,con-step w int)))
	 (implies (and (WF-rel s w)
		       (not (WF-rel u v)))
		  (and (WF-rel s v)
		       (e0-ord-< (,con-rank v)
				 (,con-rank w))))))

     (in-theory (disable b-is-a-wf-bisim-core))

     (defthm con-to-abs-type
       (,abs-p (,con-to-abs x)))

     (defthm abs-step-type
       (,abs-p (,abs-step x int)))

     (defthm con-step-type
       (,con-p (,con-step x int)))

     (defthm con-not-abs
       (implies (,con-p x)
		(not (,abs-p x))))

     (defthm abs-not-con
       (implies (,abs-p x)
		(not (,con-p x))))))

(defmacro wrap-it-up (abs-step abs-p con-step con-p
			       good-con con-to-abs con-rank)
  `(encapsulate
    ()

    (encapsulate
     ()
     (local (in-theory nil))

     (local (in-theory (enable abs-step-type con-step-type con-not-abs abs-not-con
			       con-to-abs-type
			       Wf-rel-fc B-fc
			       b-is-a-wf-bisim-core)))

     (defequiv b
       :hints (("goal"
		:by (:functional-instance
		     encap-B-is-an-equivalence

		     (encap-abs-step ,abs-step)
		     (encap-abs-p ,abs-p)
		     (encap-con-step ,con-step)
		     (encap-con-p ,con-p)
		     (encap-con-to-abs ,con-to-abs)
		     (encap-good-con ,good-con)
		     (encap-con-rank ,con-rank)

		     (encap-wf-rel wf-rel)
		     (encap-B B))))))

    (defthm rank-well-founded
      (e0-ordinalp (rank x)))

    (defun-weak-sk exists-w-succ-for-u-weak (w u)
      (exists (v)
	(and (R w v)
	     (B u v))))

    (defun-weak-sk exists-w-succ-for-s-weak (w s)
      (exists (v)
	(and (R w v)
	     (B s v)
	     (e0-ord-< (rank v) (rank w)))))

    (encapsulate
     ()
     (local (in-theory nil))

     (defthm exists-w-succ-for-u-weak-fc
       (implies (and (R w v)
		     (B u v))
		(exists-w-succ-for-u-weak w u))
       :hints (("goal" :by exists-w-succ-for-u-weak-suff))
       :rule-classes ((:forward-chaining
		       :trigger-terms ((r w v) (b u v)
				       (exists-w-succ-for-u-weak w u)))))

     (defthm exists-w-succ-for-s-weak-fc
       (implies (and (R w v)
		     (B s v)
		     (e0-ord-< (rank v) (rank w)))
		(exists-w-succ-for-s-weak w s))
       :hints (("goal" :by exists-w-succ-for-s-weak-suff))
       :rule-classes ((:forward-chaining
		       :trigger-terms ((r w v) (b s v)
				       (exists-w-succ-for-s-weak w s))))))


    (local (in-theory nil))

    (local (in-theory (enable abs-step-type con-step-type con-not-abs abs-not-con
			      con-to-abs-type
			      exists-w-succ-for-s-weak-fc exists-w-succ-for-u-weak-fc
			      R-fc R-int-fc Wf-rel-fc B-fc rank-fc
			      r-suff b-is-a-wf-bisim-core)))

    (defthm b-is-a-wf-bisim-weak
      (implies (and (b s w)
		    (r s u))
	       (or (exists-w-succ-for-u-weak w u)
		   (and (b u w)
			(e0-ord-< (rank u) (rank s)))
		   (exists-w-succ-for-s-weak w s)))
      :hints (("goal"
	       :by (:functional-instance
		    B-is-a-WF-bisim-sk

		    (encap-abs-step ,abs-step)
		    (encap-abs-p ,abs-p)
		    (encap-con-step ,con-step)
		    (encap-con-p ,con-p)
		    (encap-con-to-abs ,con-to-abs)
		    (encap-good-con ,good-con)
		    (encap-con-rank ,con-rank)

		    (encap-R-int R-int)
		    (encap-R-witness R-witness)
		    (encap-R R)
		    (encap-wf-rel wf-rel)
		    (encap-B B)
		    (encap-rank rank)

		    (encap-exists-w-succ-for-u exists-w-succ-for-u-weak)
		    (encap-exists-w-succ-for-s exists-w-succ-for-s-weak))))
      :rule-classes nil)

    (defun-sk exists-w-succ-for-u (w u)
      (exists (v)
	(and (R w v)
	     (B u v))))

    (defun-sk exists-w-succ-for-s (w s)
      (exists (v)
	(and (R w v)
	     (B s v)
	     (e0-ord-< (rank v) (rank w)))))

    (local (in-theory nil))
    (local (in-theory (enable exists-w-succ-for-s-suff exists-w-succ-for-u-suff)))

    (defthm b-is-a-wf-bisim
      (implies (and (b s w)
		    (r s u))
	       (or (exists-w-succ-for-u w u)
		   (and (b u w)
			(e0-ord-< (rank u) (rank s)))
		   (exists-w-succ-for-s w s)))
      :hints (("goal"
	       :by (:functional-instance
		    B-is-a-WF-bisim-weak

		    (exists-w-succ-for-u-weak exists-w-succ-for-u)
		    (exists-w-succ-for-s-weak exists-w-succ-for-s))))
      :rule-classes nil)
    )
  )

