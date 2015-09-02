(in-package "ACL2")

(include-book "../gen-helper/extra") ; for documentation

;; takes a tree with brlens and returns topologically
;; equivalent tree with no brlens
(mutual-recursion
(defun remove-brlens (a)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the structurally unchanged tree now with no branch lengths.~/
;  ~/
;  Arguments:
;    (1) a - a tree

;  Details: If no branch lengths are initially present, no change results.
;           Not all branches are required to have a length."
  (declare (xargs :guard t))
  (if (consp a)
      (let ((first (remove-brlens (car a))))
        (if (consp (cdr a))
            (hons first (remove-brlens-list (cdr a)))
          (if (null (cdr a))
              (hist first)
            ;; atom (cdr a)
            (if (and (atom first)
                     (consp (car a)))
                (hist first)
              first))))
    a))

(defun remove-brlens-list (a)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the structurally unchanged list of trees now with no branch lengths.~/
;  ~/
;  Arguments:
;    (1) a - a list of trees

;  Details: If no branch lengths are initially present, no change results.
;           List can contain trees both with and without brlens."
  (declare (xargs :guard t))
  (if (consp a)
      (if (null (cdr a))
          (hist (remove-brlens (car a)))
        (if (atom (cdr a))
            (remove-brlens (car a))
          (hons (remove-brlens (car a))
                (remove-brlens-list (cdr a)))))
    nil))
)

;; flag version of above functions (may be useful if we ever prove anything)
(defun remove-brlens-flg (flg a)
  (declare (xargs :guard t))
  (if flg
      (if (consp a)
          (let ((first (remove-brlens-flg t (car a))))
            (if (consp (cdr a))
                (hons first (remove-brlens-flg nil (cdr a)))
              (if (null (cdr a))
                  (hist first)
                ;; atom (cdr a)
                (if (and (atom first)
                         (consp (car a)))
                    (hist first)
                  first))))
        a)
    (if (consp a)
      (if (null (cdr a))
          (hist (remove-brlens-flg t (car a)))
        (if (atom (cdr a))
            (remove-brlens-flg t (car a))
          (hons (remove-brlens-flg t (car a))
                (remove-brlens-flg nil (cdr a)))))
      nil)))

(defthm equal-removes
  (and (equal (remove-brlens-flg t a)
              (remove-brlens a))
       (equal (remove-brlens-flg nil a)
              (remove-brlens-list a))))

;; Determines if two trees have the same topology
(defun equal-skip-brlens (a b)
  (declare (xargs :guard t))
  (equal (remove-brlens a)
         (remove-brlens b)))


(defthm equal-skip-brlens-comm
  (implies (equal-skip-brlens a b)
           (equal-skip-brlens b a)))

(defthm equal-skip-brlens-trans
  (implies (and (equal-skip-brlens a b)
                (equal-skip-brlens b c))
           (equal-skip-brlens a c)))

(defequiv equal-skip-brlens)

;; this is not quite as general as remove-brlens, but should
;; be the same on treep-num-brlens satisfying trees.
(defun strip-branch-lengths (x)
  (declare (xargs :guard t))
  (if (atom x)
      x
    (let ((a (strip-branch-lengths (car x))))
      (if (acl2-numberp (cdr x))
          a
        (cond ((equal a (car x)) ;; these were eq tests.
               ;; Have I messed anything up by making them equal?
               (let ((b (strip-branch-lengths (cdr x))))
                 (cond ((equal b (cdr x))
                        x)
                       (t (hons a b)))))
              (t (hons a (strip-branch-lengths (cdr x)))))))))

#||
(list
 (remove-brlens '(((a b) . 3) c))
 (remove-brlens '(a . 2))
 (remove-brlens '((a . 4)))
 (remove-brlens '(a b))
 (remove-brlens '((A . 4) (b . 2)))
 (remove-brlens '((a . 4) . 2))
 (remove-brlens  '((a . 4) b))
 (remove-brlens '(a . (a . 3))) ;;bad form! we don't care what it returns
 (remove-brlens '(((a . 4) (b . 3)) . 5))
 (remove-brlens '((((a . 2) (((b . 1) (c . 3)) . 4)) . 5) (((((d . 10) (e . 9)) . 7) (f . 8)) . 6)))
 (strip-branch-lengths '((((a . 2) (((b . 1) (c . 3)) . 4)) . 5) (((((d . 10) (e . 9)) . 7) (f . 8)) . 6)))
)

(list
 (equal-skip-brlens 'a '(a . 2))
 (equal-skip-brlens 'a '((a . 4)))
 (equal-skip-brlens  '((A . 4) (b . 2)) '(a b))
 (equal-skip-brlens  '((A . 4) (b . 2)) '((a . 5) b))
 (equal-skip-brlens  '(a . 3) '((a . 4) . 2))
)

||#
