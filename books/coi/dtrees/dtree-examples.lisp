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


#|===========================================================================|#
#|                                                                           |#
#|                    Examples and non-examples of dtrees                    |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(include-book "top")

#|===========================================================================|#
#|                                                                           |#
#|                               Simplest case                               |#
#|                                                                           |#
#|===========================================================================|#

(defun d-empty ()
  '(:dtree nil nil))

(defthm d-simple-1
 (dtree::dtreep (d-empty)))

(defthm d-simple-2
 (equal (d-empty) dtree::*default*))

#|===========================================================================|#
#|                                                                           |#
#|                Simple examples with non-trivial localdeps                 |#
#|                                                                           |#
#|===========================================================================|#

;; Localdeps must be a set of true lists ordered lexicographically.
;; (Note: "true lists" includes empty sets in the sense of
;; set::empty.)

(defun d-localdeps-good ()
  '(:dtree ((bar) (foo) (:hokey :smokes))
	   nil))

(defthm d-localdeps-1
 (dtree::dtreep (d-localdeps-good)))

(defthm d-localdeps-2
 (equal (d-localdeps-good)
	(dtree::leaf '((bar) (foo) (:hokey :smokes)))))

(defun d-localdeps-bad ()
  '(:dtree ((foo bar) (bas bat))
	   nil))

(defthm d-localdeps-3
 (not (dtree::dtreep (d-localdeps-bad))))

#|===========================================================================|#
#|                                                                           |#
#|                 Simple examples with non-trivial children                 |#
#|                                                                           |#
#|===========================================================================|#

;; Note that the keys of the children don't have to be arranged in any
;; particular order.

(defun d-children-good ()
  '(:dtree nil ((:pow :dtree ((:wow :xox)) nil)
		(:foo :dtree ((:bar :bas)) nil))))

(defthm d-children-1
  (dtree::dtreep (d-children-good)))

#|===========================================================================|#
#|                                                                           |#
#|                                   Leaf                                    |#
#|                                                                           |#
#|===========================================================================|#

(defthm d-leaf-1
  (equal (dtree::leaf '((:hither) (:thither) (:yon)))
	 '(:dtree ((:hither) (:thither) (:yon)) nil)))

#|===========================================================================|#
#|                                                                           |#
#|                                 Children                                  |#
#|                                                                           |#
#|===========================================================================|#

(defthm dtree-children-1
  (equal (dtree::children (d-children-good))
	 '((:pow :dtree ((:wow :xox)) nil)
	   (:foo :dtree ((:bar :bas)) nil))))

#|===========================================================================|#
#|                                                                           |#
#|                          A more complex example                           |#
#|                                                                           |#
#|===========================================================================|#

(defun d-composed ()
  '(:dtree nil
	   ((1 :dtree nil nil)
	    (2 :dtree nil nil)
	    (:st :dtree
		 nil
		 ((:bar :dtree
			((:eeny)
			 (:meeny)
			 (:miney)
			 (:st :bar)
			 (:st :bas)
			 (:st :foo))
			((:gug :dtree nil ((:wug :dtree ((:yug)) nil)))))
		  (:bas :dtree
			((:paper) (:rock) (:scissors))
			((:pow :dtree
			       ((:wow :zow))
			       nil)
			 (:how :dtree
			       ((:brown :cow :now))
			       nil)))
		  (:bat :dtree
			((:eeny)
			 (:meeny)
			 (:miney)
			 (:st :bar)
			 (:st :bas)
			 (:st :foo))
			nil)
		  (:foo :dtree
			((:eeny)
			 (:meeny)
			 (:miney)
			 (:st :bar)
			 (:st :bas)
			 (:st :foo))
			nil))))))

(defthm d-composed-1
 (dtree::dtreep (d-composed)))

#|===========================================================================|#
#|                                                                           |#
#|                                    Get                                    |#
#|                                                                           |#
#|===========================================================================|#

(defthm d-get-1
  (equal
   (dtree::get '(:st) (d-composed))
   '(:dtree nil
	    ((:bar :dtree
		   ((:eeny)
		    (:meeny)
		    (:miney)
		    (:st :bar)
		    (:st :bas)
		    (:st :foo))
		   ((:gug :dtree nil ((:wug :dtree ((:yug)) nil)))))
	     (:bas :dtree ((:paper) (:rock) (:scissors))
		   ((:pow :dtree ((:wow :zow)) nil)
		    (:how :dtree ((:brown :cow :now)) nil)))
	     (:bat :dtree
		   ((:eeny)
		    (:meeny)
		    (:miney)
		    (:st :bar)
		    (:st :bas)
		    (:st :foo))
		   nil)
	     (:foo :dtree
		   ((:eeny)
		    (:meeny)
		    (:miney)
		    (:st :bar)
		    (:st :bas)
		    (:st :foo))
		   nil)))))

(defthm d-get-2
  (equal
   (dtree::get '(:st :bar) (d-composed))
   '(:dtree ((:eeny)
	     (:meeny)
	     (:miney)
	     (:st :bar)
	     (:st :bas)
	     (:st :foo))
	    ((:gug :dtree nil ((:wug :dtree ((:yug)) nil)))))))

(defthm d-get-3
  (equal
   (dtree::get '(:st :bar :gug) (d-composed))
   '(:dtree nil ((:wug :dtree ((:yug)) nil)))))

(defthm d-get-4
  (equal
   (dtree::get '(:st :bar :gug :wug) (d-composed))
   '(:dtree ((:yug)) nil)))

#|===========================================================================|#
#|                                                                           |#
#|                                 Getchild                                  |#
#|                                                                           |#
#|===========================================================================|#

;; Getchild is the same as get on a path of length one.

#+from-child-lisp
(defthm getchild-is-get-of-singleton-list
  (equal (getchild a dtree)
         (get (list a) dtree))
  :hints(("Goal" :in-theory (enable in getchild get))))

#|===========================================================================|#
#|                                                                           |#
#|                                    Set                                    |#
#|                                                                           |#
#|===========================================================================|#

(defthm d-set-1
  (equal (dtree::set '(:key)
		     (dtree::leaf '((:hither) (:thither) (:yon)))
		     (d-empty))
	 '(:dtree nil
		  ((:key :dtree ((:hither) (:thither) (:yon)) nil)))))

(defthm d-set-2
  (equal (dtree::set '(:foo :eeny) (d-children-good) (d-composed))
	 '(:dtree nil
		  ((:foo :dtree nil
			 ((:eeny :dtree nil
				 ((:pow :dtree ((:wow :xox)) nil)
				  (:foo :dtree ((:bar :bas)) nil)))))
		   (1 :dtree nil nil)
		   (2 :dtree nil nil)
		   (:st :dtree nil
			((:bar :dtree
			       ((:eeny)
				(:meeny)
				(:miney)
				(:st :bar)
				(:st :bas)
				(:st :foo))
			       ((:gug :dtree
				      nil ((:wug :dtree ((:yug)) nil)))))
			 (:bas :dtree ((:paper) (:rock) (:scissors))
			       ((:pow :dtree ((:wow :zow)) nil)
				(:how :dtree ((:brown :cow :now)) nil)))
			 (:bat :dtree
			       ((:eeny)
				(:meeny)
				(:miney)
				(:st :bar)
				(:st :bas)
				(:st :foo))
			       nil)
			 (:foo :dtree
			       ((:eeny)
				(:meeny)
				(:miney)
				(:st :bar)
				(:st :bas)
				(:st :foo))
			       nil)))))))

#|===========================================================================|#
#|                                                                           |#
#|                                Leafdomain                                 |#
#|                                                                           |#
#|===========================================================================|#

;; Follow the paths through keys of the nested children alists to get
;; the leafdomain.
;;
(defthm d-leafdomain-1
  (equal (dtree::leafdomain (d-composed))
	 '((1)
	   (2)
	   (:st :bar :gug :wug)
	   (:st :bas :how)
	   (:st :bas :pow)
	   (:st :bat)
	   (:st :foo))))

(defthm d-leafdomain-2
  (equal
   (dtree::leafdomain
    (dtree::set '(:new :path) (d-localdeps-good) (d-composed)))
   '((1)
     (2)
     (:new :path)
     (:st :bar :gug :wug)
     (:st :bas :how)
     (:st :bas :pow)
     (:st :bat)
     (:st :foo))))

;; Note that since (d-children-good) itself has paths, they are
;; appended to '(:new :path)

(defthm d-leafdomain-3
  (equal
   (dtree::leafdomain
    (dtree::set '(:new :path) (d-children-good) (d-composed)))
   '((1)
     (2)
     (:new :path :foo)
     (:new :path :pow)
     (:st :bar :gug :wug)
     (:st :bas :how)
     (:st :bas :pow)
     (:st :bat)
     (:st :foo))))

#| In the context of book GRAPH the following theorem can be proved.

(defthm gkeys=leafdomain
 (equal (cpath::gkeys (d-composed))
	(dtree::leafdomain (d-composed))))
 |#

;; Warning: the leafdomain of the trivial dtree is not nil, but
;; (list nil).
;;
(defthm d-leafdomain-4
  (equal (dtree::leafdomain dtree::*default*)
	 '(nil)))

#|===========================================================================|#
#|                                                                           |#
#|                                  Domain                                   |#
#|                                                                           |#
#|===========================================================================|#

;; To my understanding, the domain of a dtree is the union of all
;; initial sublists of elements of its leafdomain (arranged in
;; lexicographic order).
;;
(defthm d-domain-1
  (equal (dtree::domain (d-composed))
	 '(nil (1)
	       (2)
	       (:st)
	       (:st :bar)
	       (:st :bar :gug)
	       (:st :bar :gug :wug)
	       (:st :bas)
	       (:st :bas :how)
	       (:st :bas :pow)
	       (:st :bat)
	       (:st :foo))))

#|===========================================================================|#
#|                                                                           |#
#|                                  Remove                                   |#
#|                                                                           |#
#|===========================================================================|#

;; (dtree::remove path dtree) removes path entirely from dtree.

;; This prunes the path '(:st :bas :how) leaving '(:st :bas :pow) in
;; the gkeys of (d-composed), just as I'd expect.
;;
(defthm d-remove-1
  (equal
   (dtree::remove '(:st :bas :how) (d-composed))
   '(:dtree nil
	    ((:st :dtree nil
		  ((:bas :dtree
			 nil ((:pow :dtree ((:wow :zow)) nil)))
		   (:bar :dtree
			 ((:eeny)
			  (:meeny)
			  (:miney)
			  (:st :bar)
			  (:st :bas)
			  (:st :foo))
			 ((:gug :dtree
				nil ((:wug :dtree ((:yug)) nil)))))
		   (:bat :dtree
			 ((:eeny)
			  (:meeny)
			  (:miney)
			  (:st :bar)
			  (:st :bas)
			  (:st :foo))
			 nil)
		   (:foo :dtree
			 ((:eeny)
			  (:meeny)
			  (:miney)
			  (:st :bar)
			  (:st :bas)
			  (:st :foo))
			 nil)))
	     (1 :dtree nil nil)
	     (2 :dtree nil nil)))))

;; I would expect that the path '(:st :bar :gug :wug) would be pruned
;; at :wug, leaving everthing else associated with '(:st :bar :gug)
;; alone, but what happens is that everything associated with the gkey
;; (:st :bar) is removed.  It's true that '(:st :bar :gug :wug) is the
;; only gkey rooted at (:st :bar), but why doesn't the rest of the
;; sub-dtree associated with '(:st :bar) count?
;;
(defthm d-remove-2
  (equal
   (dtree::remove '(:st :bar :gug :wug) (d-composed))
   '(:dtree nil
                ((:st :dtree nil
                      ((:bas :dtree ((:paper) (:rock) (:scissors))
                             ((:pow :dtree ((:wow :zow)) nil)
                              (:how :dtree ((:brown :cow :now)) nil)))
                       (:bat :dtree
                             ((:eeny)
                              (:meeny)
                              (:miney)
                              (:st :bar)
                              (:st :bas)
                              (:st :foo))
                             nil)
                       (:foo :dtree
                             ((:eeny)
                              (:meeny)
                              (:miney)
                              (:st :bar)
                              (:st :bas)
                              (:st :foo))
                             nil)))
                 (1 :dtree nil nil)
                 (2 :dtree nil nil)))))

;; Maybe this is the answer to the question above.  A path that leads
;; to no associated value may as well not be in the dtree: a "get" on
;; the path will yield the same answer either way.  After the remove,
;; the localdeps are all associated with nil, so they may as well not
;; appear.
;;
(defthm d-remove-3
  (and (equal (dtree::get '(:st :bar :eeny) (d-composed)) '(:dtree nil nil))
       (equal (dtree::get '(:st :bar :eeny)
			  (dtree::remove '(:st :bar :gug :wug) (d-composed)))
	      (dtree::get '(:st :bar :eeny)
			  (d-composed)))))

;; Here's what happens when you remove a non-leaf path: every path
;; extending it is pruned.
;;
(defthm d-remove-4
  (equal (dtree::remove '(:st :bas) (d-composed))
	 '(:dtree nil
		  ((:st :dtree nil
			((:bar :dtree
			       ((:eeny)
				(:meeny)
				(:miney)
				(:st :bar)
				(:st :bas)
				(:st :foo))
			       ((:gug :dtree
				      nil ((:wug :dtree ((:yug)) nil)))))
			 (:bat :dtree
			       ((:eeny)
				(:meeny)
				(:miney)
				(:st :bar)
				(:st :bas)
				(:st :foo))
			       nil)
			 (:foo :dtree
			       ((:eeny)
				(:meeny)
				(:miney)
				(:st :bar)
				(:st :bas)
				(:st :foo))
			       nil)))
		   (1 :dtree nil nil)
		   (2 :dtree nil nil)))))

#|===========================================================================|#
#|                                                                           |#
#|                                   Erase                                   |#
#|                                                                           |#
#|===========================================================================|#

;; Follow the path '(:bar :st :wug) through the nested alists and
;; replace the associated dtree '(:dtree ((:gug)) nil) with the empty
;; dtree '(:dtree nil nil)
;;
(defthm d-erase-1
  (equal (dtree::erase '(:st :bar :gug :wug) (d-composed))
	 '(:dtree nil
		  ((:st :dtree nil
			((:bar :dtree
			       ((:eeny)
				(:meeny)
				(:miney)
				(:st :bar)
				(:st :bas)
				(:st :foo))
			       ((:gug :dtree nil ((:wug :dtree nil nil)))))
			 (:bas :dtree ((:paper) (:rock) (:scissors))
			       ((:pow :dtree ((:wow :zow)) nil)
				(:how :dtree ((:brown :cow :now)) nil)))
			 (:bat :dtree
			       ((:eeny)
				(:meeny)
				(:miney)
				(:st :bar)
				(:st :bas)
				(:st :foo))
			       nil)
			 (:foo :dtree
			       ((:eeny)
				(:meeny)
				(:miney)
				(:st :bar)
				(:st :bas)
				(:st :foo))
			       nil)))
		   (1 :dtree nil nil)
		   (2 :dtree nil nil)))))
