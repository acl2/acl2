
(in-package "ACL2")

(include-book "std/lists/rev" :dir :system)
(include-book "alist-equiv")

;; Defines hons-remove-dups, which is equivalent to remove-duplicates-equal but
;; uses hashing for scalability.

(defun hons-remove-dups1 (l tab)
  (declare (xargs :guard (alistp tab)))
  (cond ((atom l) (alist-keys (fast-alist-free tab)))
        ((hons-get (car l) tab)
         (hons-remove-dups1 (cdr l) tab))
        (t (hons-remove-dups1 (cdr l) (hons-acons (car l) t tab)))))

(local (defthm member-append
         (iff (member x (append a b))
              (or (member x a)
                  (member x b)))))

(defthm remove-duplicates-equal-of-append
  (equal (remove-duplicates-equal (append a b))
         (append (set-difference-equal (remove-duplicates-equal a) b)
                 (remove-duplicates-equal b)))
  :hints(("Goal" :in-theory (enable set-difference-equal))))

(defthm set-difference-equal-append
  (equal (set-difference-equal (append a b) c)
         (append (set-difference-equal a c)
                 (set-difference-equal b c)))
  :hints(("Goal" :in-theory (enable set-difference-equal))))

(defthm set-difference-equal-remove-inside-set-difference
  (implies (member-equal k keys)
           (equal (set-difference-equal
                   (set-difference-equal a (list k))
                   keys)
                  (set-difference-equal a keys)))
  :hints(("Goal" :in-theory (enable set-difference-equal))))

(defthm hons-remove-dups1-is-remove-duplicates
  (equal (hons-remove-dups1 lst tab)
         (append (set-difference-equal
                  (remove-duplicates-equal (rev lst))
                  (alist-keys tab))
                 (alist-keys tab)))
  :hints(("Goal" :in-theory (enable rev set-difference-equal))))


(defn hons-remove-dups (l)
  (hons-remove-dups1 (rev l) nil))

(local (defthm list-fix-to-append
         (equal (list-fix x)
                (append x nil))))

(local (in-theory (disable append-of-nil)))

(local (Defthm set-difference-equal-nil
         (equal (set-difference-equal x nil)
                (list-fix x))
         :hints(("Goal" :in-theory (enable set-difference-equal)))))

(defthm hons-remove-dups-is-remove-duplicates
  (equal (hons-remove-dups l)
         (remove-duplicates-equal l)))


(in-theory (disable hons-remove-dups))
