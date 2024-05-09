(in-package "DM")

(include-book "sym")
(local (include-book "rtl/rel11/lib/top" :dir :system))

;; A permutation that transposes 2 elements:

(defun transpose-aux (i j l)
  (if (consp l)
      (if (equal (car l) i)
          (cons j (transpose-aux i j (cdr l)))
	(if (equal (car l) j)
            (cons i (transpose-aux i j (cdr l)))
          (cons (car l) (transpose-aux i j (cdr l)))))
    ()))

(defund transpose (i j n)
  (transpose-aux i j (ninit n)))

;; Characterization of suitable arguments of transpose:
;; (The purpose of the definition is to avoid typing the conditions repeatedly)

(defun trans-args-p (i j n)
  (and (posp n) (natp i) (natp j) (< i n) (< j n) (not (= i j))))

(local-defthm member-transpose-aux
  (iff (member-equal k (transpose-aux i j l))
       (if (equal k i)
           (member-equal j l)
	 (if (equal k j)
	     (member-equal i l)
	   (member-equal k l)))))

(local-defthm member-transpose
  (implies (trans-args-p i j n)
           (iff (member-equal k (transpose i j n))
                (member-equal k (ninit n))))
  :hints (("Goal" :in-theory (enable member-ninit transpose))))

(local-defthmd sublistp-transpose-1
  (implies (and (trans-args-p i j n)
                (sublistp l (ninit n)))
           (sublistp l (transpose i j n)))
  :hints (("Goal" :induct (len l))))

(local-defthmd sublistp-transpose-2
  (implies (and (trans-args-p i j n)
                (sublistp l (transpose i j n)))
           (sublistp l (ninit n)))
  :hints (("Goal" :induct (len l))))

(local-defthm sublistp-transpose
  (implies (trans-args-p i j n)
           (and (sublistp (ninit n) (transpose i j n))
	        (sublistp (transpose i j n) (ninit n))))
  :hints (("Goal" :use ((:instance sublistp-transpose-1 (l (ninit n)))
                        (:instance sublistp-transpose-2 (l (transpose i j n)))))))

(local-defthm dlistp-transpose-aux
  (implies (dlistp l)
           (dlistp (transpose-aux i j l))))

(local-defthm dlist-transpose
  (dlistp (transpose i j n))
  :hints (("Goal" :in-theory (enable transpose))))

(defthmd permp-transpose
  (implies (trans-args-p i j n)
           (in (transpose i j n) (sym n)))
  :hints (("Goal" :in-theory (enable permp permp-slist))))

(local-defthm nth-transpose-aux
  (implies (and (dlistp l) (natp k) (< k (len l)))
           (equal (nth k (transpose-aux i j l))
	          (if (equal (nth k l) i)
		      j
		    (if (equal (nth k l) j)
		        i
		      (nth k l))))))

(defthmd transpose-vals
  (implies (and (trans-args-p i j n)
                (natp k) (< k n))
	   (equal (nth k (transpose i j n))
	          (if (= k i) j
		      (if (= k j) i
		          k))))
  :hints (("Goal" :in-theory (enable transpose))))

(defthmd transpose-transpose
  (implies (trans-args-p i j n)
           (equal (transpose i j n)
	          (transpose j i n)))
  :hints (("Goal" :in-theory (enable transpose-vals)
                 :use (permp-transpose
		       (:instance permp-transpose (i j) (j i))
		       (:instance nth-diff-perm (x (transpose i j n)) (y (transpose j i n)))))))

(defthmd transpose-involution
  (implies (trans-args-p i j n)
           (equal (comp-perm (transpose i j n) (transpose i j n) n)
	          (ninit n)))
  :hints (("Goal" :in-theory (enable transpose-vals)
                  :use (permp-transpose
		       (:instance permp-transpose (i j) (j i))
		       (:instance nth-diff-perm (x (comp-perm (transpose i j n) (transpose i j n) n)) (y (ninit n)))))))

;;-----------------------------------------------------------------------------------------------------------------------------------

;; The least index that is moved by a permutation:

(defun least-moved-aux (p k)
  (if (and (consp p) (equal (car p) k))
      (least-moved-aux (cdr p) (1+ k))
    k))

(defun least-moved (p)
  (least-moved-aux p 0))

(local-defthmd least-moved-aux-bounds
  (let ((m (least-moved-aux p k)))
    (implies (natp k)
             (and (natp m)
	          (>= m k)
		  (<= m (+ k (len p)))))))

(local-defthm least-moved-aux-moved
  (let ((m (least-moved-aux p k)))
    (implies (and (natp k)
                  (< m (+ k (len p))))
	     (not (equal (nth (- m k) p) m))))
  :hints (("Subgoal *1/1" :use ((:instance least-moved-aux-bounds (k (1+ k)) (p (cdr p)))))))

(local-defthm least-moved-aux-least
  (let ((m (least-moved-aux p k)))
    (implies (and (natp k)
                  (natp n)
		  (>= n k)
                  (< n m))
	     (equal (nth (- n k) p) n)))
  :hints (("Subgoal *1/1" :use ((:instance least-moved-aux-bounds (k (1+ k)) (p (cdr p)))))))

(defthmd least-moved-bounds
  (let ((m (least-moved p)))
    (and (natp m)
         (<= m (len p))))
  :hints (("Goal" :use ((:instance least-moved-aux-bounds (k 0))))))

(defthm least-moved-moved
  (let ((m (least-moved p)))
    (implies (< m (len p))
	     (not (equal (nth m p) m))))
  :hints (("Goal" :use ((:instance least-moved-aux-moved (k 0))))))

(defthm least-moved-least
  (implies (and (natp n)
                (< n (least-moved p)))
           (equal (nth n p) n))
  :hints (("Goal" :use ((:instance least-moved-aux-least (k 0))))))

(in-theory (disable least-moved))

(defthmd least-moved-transpose
  (implies (trans-args-p i j n)
           (equal (least-moved (transpose i j n))
	          (min i j)))
  :hints (("Goal" :in-theory (enable len-perm transpose-vals)
                  :use (permp-transpose
		        (:instance least-moved-bounds (p (transpose i j n)))
		        (:instance least-moved-moved (p (transpose i j n)))
		        (:instance least-moved-least (p (transpose i j n)) (n i))
		        (:instance least-moved-least (p (transpose i j n)) (n j))))))

(defthmd least-moved-n-ninit
  (implies (and (posp n)
                (in p (sym n))
		(>= (least-moved p) n))
	   (equal (ninit n) p))
  :hints (("Goal" :use ((:instance nth-diff-perm (x p) (y (ninit n)))
                        (:instance least-moved-least (n (nth-diff p (ninit n))))))))


;;-----------------------------------------------------------------------------------------------------------------------------------

;; Transposition recognizer:

(defund transp (p n)
  (let ((m (least-moved p)))
    (and (trans-args-p m (nth m p) n)
         (equal p (transpose m (nth m p) n)))))

(defthmd permp-transp
  (implies (and (posp n) (transp p n))
           (in p (sym n)))
  :hints (("Goal" :in-theory (enable transp)
                  :use ((:instance permp-transpose (i (least-moved p)) (j (nth (least-moved p) p)))))))

(defthmd transp-transpose
  (implies (trans-args-p i j n)
           (transp (transpose i j n) n))
  :hints (("Goal" :in-theory (enable transp transpose-vals)
                  :use (least-moved-transpose transpose-transpose))))

(local-defthm trans-args-p-transpose-least-moved
  (let ((m (least-moved p)))
    (implies (and (posp n)
                  (in p (sym n))
                  (< m n))
             (trans-args-p m (nth m p) n)))
  :hints (("Goal" :in-theory (enable len-perm)
	          :use (least-moved-bounds least-moved-moved
		        (:instance permp-transpose (i (least-moved p)) (j (nth (least-moved p) p)))
		        (:instance nth-perm-ninit (x p) (k (least-moved p)))))))

(local-defthm transp-transpose-least-moved
  (let ((m (least-moved p)))
    (implies (and (posp n)
                  (in p (sym n))
                  (< m n))
             (transp (transpose m (nth m p) n) n)))
  :hints (("Goal" :in-theory (enable transp-transpose))))

(local-defthmd permp-transpose-least-moved
  (let ((m (least-moved p)))
    (implies (and (posp n)
                  (in p (sym n))
                  (< m n))
             (in (transpose m (nth m p) n) (sym n))))
  :hints (("Goal" :use ((:instance permp-transpose (i (least-moved p)) (j (nth (least-moved p) p)))))))

(defun trans-list-p (l n)
  (if (consp l)
      (and (transp (car l) n) (trans-list-p (cdr l) n))
    t))

(defthmd permp-trans-list
  (implies (and (posp n) (trans-list-p l n))
           (in (comp-perm-list l n) (sym n)))
  :hints (("subgoal *1/2" :use ((:instance permp-transp (p (car l)))))))


;;-----------------------------------------------------------------------------------------------------------------------------------

;; We shall prove constructively that every permutastion is a product of transpositions.
;; The construction uses a measure based on least-moved:

(in-theory (enable dlistp-perm))

(local-defthmd perm-meas-dec-1
  (let ((m (least-moved p)))
    (implies (and (posp n)
                  (in p (sym n))
                  (< m n)
		  (natp k)
		  (<= k m))
               (equal (nth k (comp-perm (transpose m (nth m p) n) p n))
	              k)))
  :hints (("Goal" :in-theory (e/d (len-perm transpose-vals) (least-moved-least))
                  :use (least-moved-bounds least-moved-moved
		        (:instance least-moved-least (n (nth (least-moved p) p)))
		        (:instance least-moved-least (n k))
		        (:instance nth-perm-ninit (x p) (k (least-moved p)))
		        (:instance least-moved-transpose (i (least-moved p)) (j (nth (least-moved p) p)))
		        (:instance least-moved-least (p (transpose (least-moved p) (nth (least-moved p) p) n)))
		        (:instance least-moved-bounds (p (comp-perm (transpose (least-moved p) (nth (least-moved p) p) n) p n)))))))

(defthm perm-meas-dec
  (let ((m (least-moved p)))
    (implies (and (posp n)
                  (in p (sym n))
                  (< m n))
               (< (least-moved p)
	          (least-moved (comp-perm (transpose m (nth m p) n) p n)))))
  :hints (("Goal" :use ((:instance perm-meas-dec-1 (k (least-moved (comp-perm (transpose (least-moved p) (nth (least-moved p) p) n) p n))))
                        (:instance least-moved-moved (p (comp-perm (transpose (least-moved p) (nth (least-moved p) p) n) p n)))))))

(defun trans-list (p n)
  (declare (xargs :measure (nfix (- n (least-moved p)))))
  (let* ((m (least-moved p))
         (trans (transpose m (nth m p) n))
	 (comp (comp-perm trans p n)))
    (if (and (posp n)
             (in p (sym n))
	     (< m n))
        (cons trans (trans-list comp n))
      ())))

(defthmd trans-list-p-trans-list
  (implies (and (posp n) (in p (sym n)))
           (trans-list-p (trans-list p n) n)))

(defthmd perm-prod-trans
  (implies (and (posp n) (in p (sym n)))
           (equal (comp-perm-list (trans-list p n) n)
	          p))
  :hints (("Subgoal *1/3" :use (least-moved-n-ninit))
          ("Subgoal *1/1" :use (permp-transpose-least-moved))
          ("Subgoal *1/2" :in-theory (enable transpose-involution)
	                  :use (permp-transpose-least-moved trans-args-p-transpose-least-moved
	                        (:instance sym-assoc (x (transpose (least-moved p) (nth (least-moved p) p) n))
				                     (y (transpose (least-moved p) (nth (least-moved p) p) n))
						     (z p))))))

(in-theory (disable dlistp-perm))
