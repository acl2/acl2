(in-package "SMT")
(include-book "std/util/top" :dir :system)

(encapsulate
  ; A model of arrays where the values of indices and elements can
  ; be of arbitrary types.
  ; The prefix ua- stands for "untyped array"
  (((ua-element-default) => *)
   ((ua-p *) => *)
   ((ua-init *) => *)
   ((ua-store * * *) => *)
   ((ua-select * *) => *)
   ((ua-get-default-element *) => *))

  (local (define ua-element-default () nil))

  (local (define ua-alist-p ((x acl2::any-p))
    :returns (ok booleanp)
    :enabled t
    (or (not x)
	(and (consp x)
	     (consp (car x))
	     (ua-alist-p (cdr x))))
    ///
    (more-returns
      (ok :name alistp-when-ua-alist-p
	  (implies ok (alistp x))
	  :hints(("Goal" :in-theory (enable ua-alist-p)))))))

  (local (define ua-alist-fix ((x ua-alist-p))
    :returns (xx ua-alist-p)
    (if (atom x)
      nil
      (let ((hd (car x)) (tl (cdr x)))
	(cons
	  (if (consp hd)
	    hd
	    (cons nil (ua-element-default)))
	  (ua-alist-fix tl))))
    ///
    (more-returns
      (xx :name ua-alist-fix-when-ua-alist-p
	  (implies (ua-alist-p x) (equal xx x))
          :hints(("Goal" :in-theory(enable ua-alist-p))))
      (xx :name len-of-ua-alist-fix
	  (equal (len xx) (len x))))))

  (local (define ua-p ((x acl2::any-p))
    :enabled t
    (and (consp x)
	 (ua-alist-p (car x)))))

  (local (define ua-fix ((ua ua-p))
    :returns (ar2 ua-p)
    :enabled t
    (if (consp ua)
      (cons (ua-alist-fix (car ua)) (cdr ua))
      (cons nil (ua-element-default)))
    ///
    (more-returns
      (ar2 :name ua-fix-when-ua-p
	   (implies (ua-p ua) (equal ar2 ua))))))

  (local (define ua-get-default-element ((ua ua-p))
    :returns (v0 acl2::any-p)
    :enabled t
    (cdr (ua-fix ua))))

  (local (define ua-init ((default-value acl2::any-p))
    :enabled t
    (cons nil default-value)))

  (local (define ua-store ((ua ua-p) (i acl2::any-p) (e acl2::any-p))
    :enabled t
    (let ((ua (ua-fix ua)))
      (cons (acons i e (car ua)) (cdr ua)))))

  (local (define ua-select ((ua ua-p) (i acl2::any-p))
    :enabled t
    (let ((ua (ua-fix ua))
	  (a  (assoc-equal i (car ua))))
      (if a
        (cdr a)
	(cdr ua)))))

  ; The theorems that create the constraints on the functions in our signature
  (defthm ua-p-of-ua-init (ua-p (ua-init v0)))

  (defthm ua-p-of-ua-store (ua-p (ua-store ua i v)))

  (defthm ua-get-default-element-of-ua-init
    (equal (ua-get-default-element (ua-init v0)) v0))

  (defthm ua-get-default-element-of-ua-store
    (implies (ua-p ua)
             (equal (ua-get-default-element (ua-store ua i v))
		    (ua-get-default-element ua))))

  (defthm ua-select-of-ua-init (equal (ua-select (ua-init v) i) v))

  (defthm ua-select-of-ua-store-when-indices-equal
    (implies (ua-p ua)
	     (equal (ua-select (ua-store ua i v0) i) v0)))

  (defthm ua-select-of-ua-store-when-indices-not-equal
    (implies (and (ua-p ua) (not (equal i1 i0)))
	     (equal (ua-select (ua-store ua i0 v0) i1)
		    (ua-select ua i1)))))

(encapsulate
  ; A model of arrays where indices are recognized by ta-index-p, and
  ; elements are recognized by ta-element-p.
  ; The prefix ta- stands for "typed array"
  (((ta-index-p *) => *)
   ((ta-element-p *) => *)
   ((ta-p *) => *)
   ((ta-init *) => *)
   ((ta-store * * *) => *)
   ((ta-select * *) => *))

  (local (define ta-index-p (i) (natp i)))
  (local (define ta-element-p (e) (symbolp e)))
  (local (define ta-element-default ()
    :returns (v0 ta-element-p)
    'default))

  (local (define ta-element-fix ((v ta-element-p))
    :returns (vv ta-element-p)
    (if (ta-element-p v)
      v
      (ta-element-default))
    ///
    (more-returns
      (vv :name ta-element-fix-when-ta-element-p
	  (implies (ta-element-p v) (equal vv v))))))

  (local (defun-sk ta-p (ta)
    (declare (xargs :verify-guards t))
    (forall i
	    (and (ua-p ta)
		 (ta-element-p (ua-select ta i))))))

  (local (define ta-init ((v0 ta-element-p))
    (ua-init (ta-element-fix v0))
    ///
    (in-theory (disable (:e ta-init)))))

  (local (define ta-store ((ta ta-p) (i ta-index-p) (v ta-element-p))
    (if (and (ta-index-p i) (ta-element-p v) (ta-p ta))
      (ua-store ta i v)
      (ta-init (ta-element-default)))))

  (local (define ta-select ((ta ta-p) (i ta-index-p))
    (if (and (ta-index-p i) (ta-p ta))
      (ua-select ta i)
      (ta-element-default))))


  (local (defthm ua-p-when-ta-p (implies (ta-p ta) (ua-p ta))
    :hints(("Goal" :in-theory (enable ta-p)))))

  (local (defthm ta-p-of-ua-init
    (implies (ta-element-p v0)
	     (ta-p (ua-init v0)))
    :hints(("Goal" :in-theory (enable ta-p)))))


  (defthm booleanp-of-ta-index-p (booleanp (ta-index-p x)))
  (defthm booleanp-of-ta-element-p (booleanp (ta-element-p x)))
  (defthm booleanp-of-ta-p (booleanp (ta-p ta)))

  (defthm ta-p-of-ta-init (ta-p (ta-init v0))
    :hints(("Goal" :in-theory (enable ta-init))))

  (defthm ta-p-of-ta-store
    (ta-p (ta-store ta i v))
    :hints(("Goal"
      :in-theory (e/d (ta-store)
		      (ua-select-of-ua-store-when-indices-not-equal
		       ta-p-necc))
      :cases ((equal (ta-p-witness (ua-store ta i v)) i))
      :use(
	(:instance ua-select-of-ua-store-when-indices-not-equal
		   (i0 i) (v0 v) (i1 (ta-p-witness (ua-store ta i v))) (ua ta))
	(:instance ta-p-necc (i (ta-p-witness (ua-store ta i v))))))))

  (defthm ta-element-p-of-ta-select
    (ta-element-p (ta-select ta i))
    :hints(("Goal"
      :in-theory (e/d (ta-select) (ta-p-necc))
      :use((:instance ta-p-necc)))))

  (defthm ta-select-of-ta-init
    (implies (and (ta-index-p i) (ta-element-p v))
	     (equal (ta-select (ta-init v) i) v))
    :hints(("Goal" :in-theory (enable ta-select ta-init))))

  (local (defthm ta-select-of-ta-store-when-indices-equal
    (implies (and (ta-p ta) (ta-index-p i) (ta-element-p v))
	     (equal (ta-select (ta-store ta i v) i) v))
    :hints(("Goal"
      :in-theory (e/d (ta-select ta-store) (ta-p-of-ta-store))
      :use((:instance ta-p-of-ta-store))))))

  (local (defthm ta-select-of-ta-store-when-indices-not-equal
    (implies (and (ta-p ta) (ta-index-p i0) (ta-element-p v0)
		  (not (equal i1 i0)))
	     (equal (ta-select (ta-store ta i0 v0) i1)
		    (ta-select ta i1)))
    :hints(("Goal"
      :in-theory (e/d (ta-select ta-store) (ta-p-of-ta-store))
      :use((:instance ta-p-of-ta-store (i i0) (v v0)))))))

  (defthm ta-select-of-ta-store
    (implies (and (ta-p ta) (ta-index-p i0) (ta-element-p v0))
	     (equal (ta-select (ta-store ta i0 v0) i1)
		    (if (equal i1 i0)
		        v0
		        (ta-select ta i1))))))
