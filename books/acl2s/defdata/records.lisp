#|


|#


(in-package "ACL2")
(include-book "misc/total-order" :dir :system)

(defun ordered-unique-key-alistp (a)
  (declare (xargs :guard (alistp a)))
  (or (null (cdr a))
      (and (<< (caar a) (caadr a))
           (ordered-unique-key-alistp (cdr a)))))

(defun no-nil-val-alistp (a)
  (declare (xargs :guard (alistp a)))
  (or (null a)
      (and (not (null (cdar a)))
           (no-nil-val-alistp (cdr a)))))

(defun recordp (r)
  (declare (xargs :guard t))
  (and (alistp r)
       (no-nil-val-alistp r)
       (ordered-unique-key-alistp r)))
        
(defun mapp (x)
  (declare (xargs :guard t))
  (recordp x))

(defun mget (a r)
  (declare (xargs :guard (recordp r)))
  (cond ((or (atom r)
             (<< a (caar r)))
         nil)
        ((equal a (caar r))
         (cdar r))
        (t (mget a (cdr r)))))

(defun mset-cons (a v r)
  (declare (xargs :guard (recordp r)))
  (if v (acons a v r) r))

(defun mset (a v r) 
  (declare (xargs :guard (recordp r)))
  (cond ((atom r) (mset-cons a v r))
        ((<< a (caar r)) (mset-cons a v r))
        ((equal a (caar r))
         (mset-cons a v (cdr r)))
        (t (cons (car r) (mset a v (cdr r))))))

#|

(defthm s-is-bounded
  (implies (and (recordp r)
                (mset a v r)
                (<< e a)
                (<< e (caar r)))
           (<< e (caar (mset a v r)))))
|#

(defthm s-preserves-ordered-unique-key-alistp
  (implies (and (alistp r)
                (ordered-unique-key-alistp r))
           (ordered-unique-key-alistp (mset a v r)))
  :hints (("goal" :in-theory (enable <<))))

(defthm s-preserves-no-nil-val-alistp
  (implies (and (alistp r)
                (no-nil-val-alistp r))
           (no-nil-val-alistp (mset a v r)))
  :hints (("goal" :in-theory (enable <<))))

(defthm s-preserves-recordp
  (implies (recordp r)
           (recordp (mset a v r))))

(defthm recordp-implies-alistp
  (implies (recordp x)
           (alistp x))
  :rule-classes (:forward-chaining
                 :rewrite))

(defthm recordp-implies-no-nil-val-alistp
  (implies (recordp x)
           (no-nil-val-alistp x))
  :rule-classes (:forward-chaining
                 :rewrite))

(defthm recordp-implies-ordered-unique-key-alistp
  (implies (recordp x)
           (ordered-unique-key-alistp x))
  :rule-classes (:forward-chaining
                 :rewrite))

(defthm recordp-implies-true-listp
  (implies (recordp x)
           (true-listp x))
  :rule-classes (:forward-chaining
                 :rewrite))

(defthm mget-same-mset
  (implies (recordp r)
           (equal (mget a (mset a v r))
                  v)))

(defthm mget-diff-mset
  (implies (and (recordp r)
                (not (equal a b)))
           (equal (mget a (mset b v r))
                  (mget a r))))

(defthm mset-same-mget
  (implies (recordp r)
           (equal (mset a (mget a r) r)
                  r)))

(defthm mset-same-mset
  (implies (recordp r)
           (equal (mset a y (mset a x r))
                  (mset a y r))))

(defthm mset-diff-mset
  (implies (and (recordp r)
                (not (equal a b)))
           (equal (mset b y (mset a x r))
                  (mset a x (mset b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a mset)))))

(defthm mset-non-nil-cannot-be-nil
  (implies v (mset a v r)))

(defthm mget-is-nil-for-<<
  (implies (<< a (caar r))
           (equal (mget a r) nil)))

#|
(defthm mget-of-mset-expand
  (implies (recordp r)
           (equal (mget a (mset b v r))
                  (if (equal a b) v (mget a r)))))

(in-theory (disable mget-of-mset-expand))
|#

(defthm mget-of-nil-is-nil
  (not (mget a nil)))

(defthm mset-nil-is-rec
  (implies (recordp r)
           (recordp (mset k nil r))))

(defthm non-nil-if-mget-non-nil
  (implies (mget a r) r)
  :rule-classes :forward-chaining)

(defun msets-macro (r msets)
  (declare (xargs :guard (and (true-listp msets)
                              (evenp (len msets)))))
  (if (endp msets)
      r
    (msets-macro `(mset ,(car msets) ,(cadr msets) ,r)
                 (cddr msets))))

(defmacro msets (r &rest msets)
  (declare (xargs :guard (and (true-listp msets)
                              (evenp (len msets)))))
  (msets-macro r msets))

(in-theory (disable mset mget recordp ordered-unique-key-alistp
                    no-nil-val-alistp))

(deftheory extensible-records
  '(recordp
    ordered-unique-key-alistp
    no-nil-val-alistp
    mset
    mget
    <<
    ))
