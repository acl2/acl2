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

(in-package "ACL2")

;; It would be nice to do development in a package other than ACL2.
;; Then, have a macro that imports symbols into the acl2 package
;; automatically.

;; fixedpoint: Records have the property that, under certain
;; conditions, (equal (g nil r) r).  If this property does not hold,
;; then (< (acl2-count (g a r)) (acl2-count r)).  We call the property
;; the fixedpoint and here we prove some useful properties about
;; fixedpoints.

;; We define the following rule sets in conjunction with this book:
;;
;; records::aux
;; records::aux-to-export
;; records::devel
;; records::export

(include-book "domain")

(include-book "../util/rule-sets")

;; ==================================================================
;;
;; fixedpoint
;;
;; ==================================================================

(defund fixedpoint (r)
  (equal (g nil r) r))

;;
;; This is the local part of the definition of ifrp.  There
;; is a weaker condition on the record that guarantees that
;; (g nil x) decreases.
;;
(defund localfixedpoint (x)
  (or (not x)
      (not (rcdp x))
      (and (consp x)
	   (null (cdr x))
	   (consp (car x))
	   (null (caar x)))))

(defthmd abstract-localfixedpoint
  (equal (localfixedpoint x)
	 (list::subsetp (rkeys x) (list nil)))
  :hints (("Goal" :in-theory (enable
			      localfixedpoint
			      g
			      rkeys
			      acl2->rcd
			      alist::keys
			      ))))

;; This should leave you with expressions in terms of (len (rkeys x)),
;; boolean expressions over records, and expressions of the form (g
;; nil x).  I think that is a pretty nice result.  Now it's not so
;; bad to compute (fixedpoint (s a v r)) ..

;; AUX
(defthm leaf-measure-aux
  (implies
   (and
    (not (ifrp r))
    r)
   (< (acl2-count (g-aux a r)) (acl2-count r)))
  :rule-classes (:linear)
  :hints (("Goal" :induct (g-aux a r)
	   :expand (ifrp r)
	   :in-theory (enable g-aux rcdp ifrp))))

;; (rule-set records::aux leaf-measure-aux)

;; Transition
(local
(defthm leaf-measure-ifrp
  (implies
   (and
    (not (ifrp r))
    r)
   (< (acl2-count (g a r)) (acl2-count r)))
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable g ACL2->RCD)))))

;; AUX
(defthm g-aux-implies-inequality
  (implies
   (and
    (not (ifrp r))
    r)
   (not (equal (g-aux a r) r)))
  :hints (("Goal" :use leaf-measure-aux)))

;; Transition
(defthmd fixedpoint-to-ifrp
  (equal (fixedpoint r)
	 (or (ifrp r) (not r)))
  :hints (("Goal" :in-theory (enable fixedpoint g ACL2->RCD)
	   :cases ((null (g-aux nil r))))))

(defthmd abstract-fixedpoint-helper
  (equal (fixedpoint x)
	 (if (null x) t
	   (and (localfixedpoint x)
		(fixedpoint (g nil x)))))
  :rule-classes (:definition)
  :hints (("Goal" :in-theory (enable
			      localfixedpoint
			      FIXEDPOINT-TO-IFRP
			      ifrp
			      g
			      g-aux
			      acl2->rcd
			      ))))

(defthmd abstract-fixedpoint
  (equal (fixedpoint x)
	 (if (null x) t
	   (and (list::subsetp (rkeys x) (list nil))
		(fixedpoint (g nil x)))))
  :rule-classes (:definition)
  :hints (("Goal" :in-theory (enable abstract-fixedpoint-helper
				     abstract-localfixedpoint))))

(defthmd fixedpoint-impact-on-keys
  (implies
   (fixedpoint r)
   (equal (rkeys r) (if r (list nil) nil)))
  :hints (("Goal" :in-theory (e/d (IFRP
			    ALIST::KEYS
			    fixedpoint-to-ifrp
			    rkeys
			    ACL2->RCD)))))

;; Export
(defthm fixedpoint-measure
  (implies
   (not (fixedpoint r))
   (< (acl2-count (g a r)) (acl2-count r)))
  :hints (("Goal" :in-theory (enable fixedpoint-to-ifrp)))
  :rule-classes (:linear))

;; Export
(defthm fixedpoint-nil
  (implies
   (not r)
   (fixedpoint r)))

;; Export
(defthm fixedpoint-implies-fixedpoint-gar
  (implies
   (fixedpoint r)
   (fixedpoint (g a r)))
  :hints (("Goal" :use fixedpoint-to-ifrp
	   :in-theory (enable ACL2->RCD)
	   :expand ((fixedpoint (g a r))
		    (g a r)))))

;; Export (?) .. Perhaps we would be better off casting (g a r)
;; as memberp?

(defthmd fixedpoint-gar-rewrite
  (implies
   (fixedpoint r)
   (equal (g a r) (if (null a) r nil)))
  :hints (("Goal" :in-theory (enable FIXEDPOINT-TO-IFRP ACL2->RCD)
	   :expand ((g a r)))))

;;
;; This belongs in << library
;;
(defthm <<-converse
  (implies
   (and
    (NOT (<< X Y))
    (NOT (EQUAL X Y)))
   (<< Y X))
  :rule-classes (:forward-chaining))

;; AUX
(defun ifrp-s-aux (a v r)
  (if (endp r)
      (and (ifrp v) (not a))
    (if (null (cdr r))
	(if (<< a (caar r))
	    (and (not v) (ifrp r))
	  (and (null (caar r))
	       (if (null a) (ifrp v)
		 (and (not v) (ifrp r)))))
      (if (<< a (caar r)) nil
	(if (equal a (caar r))
	    (if v nil (ifrp (cdr r)))
	  (and (ifrp (list (car r)))
	       (let ((r (cdr r)))
		 (and (equal a (caar r))
		      (null v) (not (consp (cdr r)))))))))))

(defthm ifrp-s-aux-to-ifrp-s-aux
  (implies
   (rcdp r)
   (equal (ifrp (s-aux a v r))
	  (ifrp-s-aux a v r)))
  :hints (("Goal"  :in-theory (enable s-aux)
	   :do-not-induct t
	   :expand ((RCDP (CDR R))
		    (s-aux a v r)
		    (s-aux a v (cdr r))))))

(defun ifrp-s-aux-member (a v r)
  (let ((keys (alist::keys r)))
    (let ((size (len keys)))
      (cond
       ((= 0 size) (and (not a) (ifrp v)))
       ((= 1 size) (and (list::memberp nil keys)
			(if (<< a nil) (and (null v) (ifrp (g-aux nil r)))
			  (if (equal a nil) (and v (null a) (ifrp v))
			    (and (not v) (ifrp (g-aux nil r)))))))
       ((= 2 size) (and (ifrp (g-aux nil r))
			(and a (list::memberp a keys) (not v))))
       (t nil)))))

(defthm ifrp-s-aux-reformulation
  (implies
   (rcdp r)
   (equal (ifrp-s-aux a v r)
	  (ifrp-s-aux-member a v r)))
  :hints (("Goal" :do-not-induct t
	   :expand ((alist::keys r)
		    (alist::keys (cdr r)))
	   :in-theory (enable alist::keys
			      g-aux))))

(defun ifrp-s-member (a v r)
  (let ((keys (rkeys r)))
    (let ((size (len keys)))
      (cond
       ((= 0 size) (and (not a) (ifrp v)))
       ((= 1 size) (and (list::memberp nil keys)
			(if (<< a nil) (and (null v) (ifrp (g nil r)))
			  (if (equal a nil) (and v (null a) (ifrp v))
			    (and (not v) (ifrp (g nil r)))))))
       ((= 2 size) (and (ifrp (g nil r))
			(and a (list::memberp a keys) (not v))))
       (t nil)))))

(defun ifrp-s (a v r)
  (let ((keys (rkeys r)))
    (let ((size (len keys)))
      (cond
       ((= 0 size) (and (not a) (ifrp v)))
       ((= 1 size) (and (g nil r)
			(if (<< a nil) (and (null v) (ifrp (g nil r)))
			  (if (equal a nil) (and v (null a) (ifrp v))
			    (and (not v) (ifrp (g nil r)))))))
       ((= 2 size) (and (ifrp (g nil r))
			(and a (g a r) (not v))))
       (t nil)))))

(defthmd ifrp-s-to-ifrp-s-member
  (equal (ifrp-s a v r)
	 (ifrp-s-member a v r))
  :hints (("Goal" :in-theory '(ifrp-s ifrp-s-member MEMBERP-RKEYS-REDUCTION))))

(defthm ifrp-rcd->acl2
  (implies
   (rcdp x)
   (equal (ifrp (rcd->acl2 x))
	  (ifrp x)))
  :hints (("Goal" :in-theory (enable rcd->acl2))))

(defthm ifrp-s-to-ifrp-s
  (equal (ifrp (s a v r))
	 (ifrp-s a v r))
  :hints (("Goal" :in-theory (e/d (ifrp-s-to-ifrp-s-member
				   rkeys
				   g s)
				  (ifrp-s
				   ifrp-s-aux)))))

(defthm consp-keys
  (equal (consp (alist::keys list))
	 (consp list))
  :hints (("Goal" :in-theory (enable alist::keys))))

(defthm iff-s-aux-alt
  (implies
   (rcdp r)
   (iff (s-aux a v r)
	(not (or (and (not r)
		      (not V))
		 (and (equal (len (alist::keys r)) 1)
		      (list::memberp a (alist::keys r))
		      (not v))))))
  :hints (("Goal" :in-theory (enable alist::keys list::memberp))))

(defthm iff-rcd->acl2
  (implies
   (rcdp r)
   (iff (rcd->acl2 r)
	(if (ifrp r) (g nil r) r)))
  :hints (("Goal" :in-theory (enable ACL2->RCD rcd->acl2 g))))

(defthm g-aux-nil-ifrp
  (implies
   (ifrp r)
   (g-aux nil (acl2->rcd r)))
  :hints (("Goal" :in-theory (enable g-aux acl2->rcd))))

(defthm iff-acl2->rcd
  (iff (acl2->rcd r)
       (or (ifrp r) r))
  :hints (("Goal" :in-theory (enable acl2->rcd))))

(defun iff-s-member (a v r)
  (not (or (and (not (if (ifrp r) (g nil r) r))
		(not V))
	   (and (equal (len (rkeys r)) 1)
		(list::memberp a (rkeys r))
		(not v)))))

(defun iff-s-ifrp (a v r)
  (not (or (and (not (if (ifrp r) (g nil r) r))
		(not V))
	   (and (equal (len (rkeys r)) 1)
		(g a r)
		(not v)))))

(defthmd iff-s-ifrp-to-iff-s-member
  (equal (iff-s-ifrp a v r)
	 (iff-s-member a v r))
  :hints (("Goal" :in-theory '(iff-s-ifrp iff-s-member MEMBERP-RKEYS-REDUCTION))))

(defthmd iff-s-to-iff-s-ifrp
  (iff (s a v r)
       (iff-s-ifrp a v r))
  :hints (("Goal" :do-not-induct t
	   :in-theory (e/d (list::memberp-when-not-memberp-of-cdr-cheap
			    iff-s-ifrp-to-iff-s-member rkeys g s)
			   (iff-s-ifrp)))))

;; It would be interesting if (fixedpoint (s a v r)) were amenible to
;; decomposition into an expression involving only fixedpoint

(defthmd ifrp-to-fixedpoint
  (equal (ifrp r) (if (not r) nil (fixedpoint r)))
  :hints (("Goal" :in-theory (enable FIXEDPOINT-TO-IFRP))))

(theory-invariant (incompatible
		   (:rewrite ifrp-to-fixedpoint)
		   (:rewrite FIXEDPOINT-TO-IFRP)
		   ))

(defmacro ifrp-as-fixedpoint (r)
  `(if (not ,r) nil (fixedpoint ,r)))

(defun fixedpoint-s-fn (a v r)
  (or (let ((keys (rkeys r)))
	(let ((size (len keys)))
	  (cond
	   ((= 0 size) (and (not a) (ifrp-as-fixedpoint v)))
	   ((= 1 size) (and (g nil r)
			    (if (<< a nil) (and (null v) (ifrp-as-fixedpoint (g nil r)))
			      (if (null a) (and v (ifrp-as-fixedpoint v))
				(and (not v) (ifrp-as-fixedpoint (g nil r)))))))
	   ((= 2 size) (and (ifrp-as-fixedpoint (g nil r))
			    (and a (g a r) (not v))))
	   (t nil))))
      (and (not (if (ifrp-as-fixedpoint r) (g nil r) r))
	   (not V))
      (and (equal (len (rkeys r)) 1)
	   (g a r)
	   (not v))))

;; This theorem allows us to describe fixedpoints relative to
;; (s a v r) in terms of:
;;
;; - iff r
;; - iff (g a r)
;; - iff v
;; - (len (rkeys r))
;; - (fixedpoint r)
;; - (fixedpoint v)
;;
(defthmd fixedpoint-s-to-fixedpoint-s-fn
  (equal (fixedpoint (s a v r))
	 (fixedpoint-s-fn a v r))
  :hints (("Goal" :in-theory (enable iff-s-to-iff-s-ifrp
				     FIXEDPOINT-TO-IFRP))))

(defun iff-s-fixedpoint (a v r)
  (not (or (and (not (if (ifrp-as-fixedpoint r) (g nil r) r))
		(not V))
	   (and (equal (len (rkeys r)) 1)
		(g a r)
		(not v)))))

(defthmd iff-s-ifrp-to-iff-s-fixedpoint
  (equal (iff-s-ifrp a v r)
	 (iff-s-fixedpoint a v r))
  :hints (("Goal" :in-theory (enable FIXEDPOINT-TO-IFRP))))

(defthmd iff-s-to-iff-s-fixedpoint
  (iff (s a v r)
       (iff-s-fixedpoint a v r))
  :hints (("Goal" :in-theory '(iff-s-to-iff-s-ifrp
			       iff-s-ifrp-to-iff-s-fixedpoint))))

(defthmd open-abstract-fixedpoint-on-s
  (implies
   (syntaxp (equal (car x) 's))
   (equal (fixedpoint x)
	  (if (null x) t
	    (and (list::subsetp (rkeys x) (list nil))
		 (fixedpoint (g nil x))))))
  :hints (("Goal" :in-theory (enable abstract-fixedpoint))))

;; ===================================================================
;;
;; These three theorems (possibly with abstract-fixedpoint) are
;; probably the ones you want for doing fixedpoint reasoning.
;;
;; ===================================================================

(defthmd gar-as-memberp
  (iff (g a r)
       (list::memberp a (rkeys r)))
  :hints (("Goal" :in-theory (enable memberp-rkeys-reduction))))

(theory-invariant (incompatible
		   (:rewrite gar-as-memberp)
		   (:rewrite memberp-rkeys-reduction)))

;; DAG - there is some concern about opening set functions into
;; "remove" .. I think that was what was causing problems below.
;; There should be a switch in the set library to turn this off.

(defthm iff-s
  (iff (s a v r)
       (or v
	   (and r (if (acl2::fixedpoint r) a
		    (not (list::subsetp (rkeys r) (list a)))))))
  :hints (("Goal" :in-theory (e/d (iff-s-to-iff-s-fixedpoint
				   gar-as-memberp
				   fixedpoint-impact-on-keys)
				  (LIST::MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP)))
	  ("Subgoal 3''" :in-theory (enable list::memberp))))

(defthm fixedpoint-s
  (equal (fixedpoint (s a v r))
	 (or
	  ;; Results from (not (s a v r))
	  (not (or v
		   (and r (if (acl2::fixedpoint r) a
			    (not (list::subsetp (rkeys r) (list a)))))))
	  (and
	   ;; Results from (localfixedpoint (s a v r))
	   (if v (list::subsetp (cons a (rkeys r)) (list nil))
	     (list::subsetp (rkeys r) (list a nil)))
	   ;; Results from (fixedpoint (g nil (s a v r)))
	   (if (null a) (fixedpoint v)
	     (fixedpoint (g nil r))))))
  :hints (("Goal" :in-theory (e/d (rkeys-s
				   g-of-s-redux
				   iff-s
				   abstract-localfixedpoint
				   open-abstract-fixedpoint-on-s)
				  ))))
