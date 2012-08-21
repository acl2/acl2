(in-package "ACL2")

(include-book "riemann-defuns")

(defun index-for-large-element (list bound)
  (if (consp list)
      (if (>= (car list) bound)
          0
        (1+ (index-for-large-element (cdr list) bound)))
    0))

(defthm index-for-large-element-works
  (let ((index (index-for-large-element list bound)))
    (implies (< 0 bound)
             (iff (< (maxlist list) bound)
                  (or (not (< index (len list)))
                      (< (nth index list)
                         bound))))))

(encapsulate
 ()
 (local (include-book "map-rcfn-close-to-map-rcfn-refinement"))
 (defthm map-rcfn-close-to-map-rcfn-refinement
   (implies (and (strong-refinement-p p1 p2)
                 (consp (cdr p1))
                 (standard-numberp (car p1))
                 (standard-numberp (car (last p1)))
                 (i-small (mesh p2))
                 (standard-numberp r)
                 (realp r)
                 (< 0 r)
                 (<= 0 index)
                 (< index (len p1)))
            (< (abs (- (nth index (map-rcfn p1))
                       (nth index (map-rcfn-refinement p1 p2))))
               r)))
 )

(include-book "riemann-lemmas")

(defthm maxlist-abslist-difflist-maps-lt-by-index
  (implies (and (strong-refinement-p p1 p2)
                (consp (cdr p1))
                (standard-numberp (car p1))
                (standard-numberp (car (last p1)))
                (i-small (mesh p2))
                (standard-numberp r)
                (realp r)
                (< 0 r)
                (<= 0 index)
                (< index (len p1)))
           (< (nth index (abslist
                          (difflist
                           (map-rcfn p1)
                           (map-rcfn-refinement p1 p2))))
              r))
  :hints (("Goal" :in-theory (disable map-rcfn map-rcfn-refinement
                                      strong-refinement-p mesh abs
                                      nth abslist difflist))))

(defthm maxlist-abslist-difflist-maps-lt
  (implies (and (strong-refinement-p p1 p2)
                (consp (cdr p1))
                (standard-numberp (car p1))
                (standard-numberp (car (last p1)))
                (i-small (mesh p2))
                (standard-numberp r)
                (realp r)
                (< 0 r))
           (< (maxlist
               (abslist
                (difflist
                 (map-rcfn p1)
                 (map-rcfn-refinement p1 p2))))
              r))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable maxlist abslist difflist abs
                                      map-rcfn map-rcfn-refinement
                                      strong-refinement-p))))
