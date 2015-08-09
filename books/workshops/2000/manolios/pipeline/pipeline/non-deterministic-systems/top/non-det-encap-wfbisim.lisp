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
(include-book "../../top/defun-weak-sk")
(include-book "../../../../../../../ordinals/e0-ordinal")

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

(encapsulate
 ((encap-abs-step (abs int) t)
  (encap-abs-p (abs) t)
  (encap-con-step (con int) t)
  (encap-con-p (con) t)
  (encap-con-to-abs (con) t)
  (encap-good-con (con) t)
  (encap-con-rank (con) t))

 (local (defun encap-abs-step (abs int)
	  (declare (ignore abs int))
	  t))

 (local (defun encap-abs-p (abs)
	  (equal abs t)))

 (local (defun encap-con-step (con int)
	  (declare (ignore con int))
	  nil))

 (local (defun encap-con-p (con)
	  (equal con nil)))

 (local (defun encap-con-to-abs (con)
	  (declare (ignore con))
	  t))

 (local (defun encap-good-con (con)
	  (declare (ignore con))
	  t))

 (local (defun encap-con-rank (con)
	  (declare (ignore con))
	  0))

 (defun encap-WF-rel (x y)
   (and (encap-abs-p x) ;not needed, but helps with case analysis
	(encap-con-p y)
	(encap-good-con y)
	(equal x (encap-con-to-abs y))))

 (defthm encap-B-is-a-WF-bisim-core
   (let ((u (encap-abs-step s int))
	 (v (encap-con-step w int)))
     (implies (and (encap-wf-rel s w)
		   (not (encap-wf-rel u v)))
	      (and (encap-wf-rel s v)
		   (e0-ord-< (encap-con-rank v)
			     (encap-con-rank w)))))
   :rule-classes nil)

 (defthm encap-abs-step-type
   (encap-abs-p (encap-abs-step x int)))

 (defthm encap-con-step-type
   (encap-con-p (encap-con-step x int)))

 (defthm encap-con-not-abs
   (implies (encap-con-p x)
	    (not (encap-abs-p x))))

 (defthm encap-abs-not-con
   (implies (encap-abs-p x)
	    (not (encap-con-p x))))

 (defthm encap-con-to-abs-type
   (encap-abs-p (encap-con-to-abs x)))
 )

(defun encap-R-int (x y int)
  (cond ((encap-abs-p x)
	 (equal y (encap-abs-step x int)))
	(t (equal y (encap-con-step x int)))))

(defun-sk encap-R (x y)
  (exists (int)
    (encap-R-int x y int)))

(defun encap-B (x y)
  (bor (encap-WF-rel x y)
       (encap-WF-rel y x)
       (equal x y)
       (and (encap-con-p x)
	    (encap-con-p y)
	    (encap-good-con x)
	    (encap-good-con y)
	    (equal (encap-con-to-abs x)
		   (encap-con-to-abs y)))))

(defequiv encap-B)

(defun encap-rank (x)
  (if (encap-con-p x)
      (encap-con-rank x)
    0))

(defun encap-take-appropriate-step (w int)
  (cond ((encap-abs-p w)
	 (encap-abs-step w int))
	(t (encap-con-step w int))))

(defthm type-fc
  (implies (equal u (encap-con-step s int))
	   (encap-con-p u)))

(defthm encap-B-is-a-WF-bisim-0
  (implies (and (encap-WF-rel s w)
		(encap-R-int s u int))
	   (bor (encap-B u (encap-take-appropriate-step w int))
		(and (encap-B u w)
		     (e0-ord-< (encap-rank u) (encap-rank s)))
		(and (encap-B s (encap-take-appropriate-step w int))
		     (e0-ord-< (encap-rank (encap-take-appropriate-step w int))
			       (encap-rank w)))))
  :hints (("goal"
	   :use (:instance encap-B-is-a-WF-bisim-core)))
  :rule-classes nil)

(defthm encap-B-is-a-WF-bisim-1
  (implies (and (encap-WF-rel w s)
		(encap-R-int s u int))
	   (bor (encap-B u (encap-take-appropriate-step w int))
		(and (encap-B u w)
		     (e0-ord-< (encap-rank u) (encap-rank s)))
		(and (encap-B s (encap-take-appropriate-step w int))
		     (e0-ord-< (encap-rank (encap-take-appropriate-step w int))
			       (encap-rank w)))))
  :hints (("goal"
	   :use (:instance encap-B-is-a-WF-bisim-core (s w) (w s))))
  :rule-classes nil)

(defthm encap-B-is-a-WF-bisim-2
  (implies (and (equal s w)
		(encap-R-int s u int))
	   (bor (encap-B u (encap-take-appropriate-step w int))
		(and (encap-B u w)
		     (e0-ord-< (encap-rank u) (encap-rank s)))
		(and (encap-B s (encap-take-appropriate-step w int))
		     (e0-ord-< (encap-rank (encap-take-appropriate-step w int))
			       (encap-rank w)))))
  :rule-classes nil)

(defthm encap-B-is-a-WF-bisim-3
  (implies (and (encap-con-p s)
		(encap-con-p w)
		(encap-good-con s)
		(encap-good-con w)
		(equal (encap-con-to-abs s)
		       (encap-con-to-abs w))
		(encap-R-int s u int))
	   (bor (encap-B u (encap-take-appropriate-step w int))
		(and (encap-B u w)
		     (e0-ord-< (encap-rank u) (encap-rank s)))
		(and (encap-B s (encap-take-appropriate-step w int))
		     (e0-ord-< (encap-rank (encap-take-appropriate-step w int))
			       (encap-rank w)))))
  :hints (("goal"
	   :use ((:instance encap-B-is-a-WF-bisim-core (w (encap-con-to-abs s)))
		 (:instance encap-B-is-a-WF-bisim-core (s (encap-con-to-abs w)))
		 (:instance encap-B-is-a-WF-bisim-core (w s) (s (encap-con-to-abs w)))
		 (:instance encap-B-is-a-WF-bisim-core (w (encap-con-to-abs w)) (s w)))))
  :rule-classes nil)

(defthm encap-B-is-a-WF-bisim
  (implies (and (encap-B s w)
		(encap-R-int s u int))
	   (bor (encap-B u (encap-take-appropriate-step w int))
		(and (encap-B u w)
		     (e0-ord-< (encap-rank u) (encap-rank s)))
		(and (encap-B s (encap-take-appropriate-step w int))
		     (e0-ord-< (encap-rank (encap-take-appropriate-step w int))
			       (encap-rank w)))))
  :hints (("goal"
	   :use ((:instance encap-b (x s) (y w))
		 (:instance encap-B-is-a-WF-bisim-0)
		 (:instance encap-B-is-a-WF-bisim-1)
		 (:instance encap-B-is-a-WF-bisim-2)
		 (:instance encap-B-is-a-WF-bisim-3))
	   :in-theory (disable encap-wf-rel encap-r
			       encap-take-appropriate-step encap-rank e0-ord-< encap-b)))
  :rule-classes nil)

(defun-weak-sk encap-exists-w-succ-for-u (w u)
  (exists (v)
    (and (encap-R w v)
	 (encap-B u v))))

(defun-weak-sk encap-exists-w-succ-for-s (w s)
  (exists (v)
    (and (encap-R w v)
	 (encap-B s v)
	 (e0-ord-< (encap-rank v) (encap-rank w)))))

(defthm R-int-take-step
  (encap-R-int w (encap-take-appropriate-step w int) int))

(defthm R-take-step
  (encap-R w (encap-take-appropriate-step w int))
  :hints (("goal"
	   :use (:instance R-int-take-step)
	   :in-theory (disable encap-r-int R-int-take-step))))

(in-theory (disable encap-B encap-R-int encap-rank encap-take-appropriate-step))

(defthm B-is-a-WF-bisim-sk
  (implies (and (encap-B s w)
		(encap-R s u))
	   (or (encap-exists-w-succ-for-u w u)
	       (and (encap-B u w)
		    (e0-ord-< (encap-rank u) (encap-rank s)))
	       (encap-exists-w-succ-for-s w s)))
  :hints (("goal"
	   :use ((:instance encap-B-is-a-WF-bisim (int (encap-r-witness s u)))
		 (:instance encap-exists-w-succ-for-u-suff
			    (v (encap-take-appropriate-step w (encap-r-witness s u))))
		 (:instance encap-exists-w-succ-for-s-suff
			    (v (encap-take-appropriate-step w (encap-r-witness s u)))))))
  :rule-classes nil
  :otf-flg t)
