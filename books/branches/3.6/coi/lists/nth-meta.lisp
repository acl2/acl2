#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(defun unhide (x)
  (declare (type t x))
  x)

(defthm unhide-hide
 (equal (unhide (hide x))
     x)
 :hints (("Goal" :expand ((hide x)))))

(in-theory (disable unhide))


;reordered these two rules, since we want the second one to fire first

(defevaluator nth-update-nth-eval nth-update-nth-eval-lst
  ((nth x l)
   (update-nth n v l)
   (hide x)
   (unhide x)
;   (skip-rewrite x)
   ))


;; :meta rule to quickly strip off irrelevant update-nths in an "nth of
;; update-nth nest" situation when the relevant indices are constants
;;



;n is a numeric value
;term is a nest of update-nths
;we return an equivalent nest that agrees with TERM for nth of n.
(defun drop-irrelevant-update-nth-calls-from-update-nth-nest-aux (n term changed-anything-flg)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term))
      (if changed-anything-flg term nil)
    (if (and (equal 'update-nth (car term))
             (quotep (cadr term))
             (natp (cadr (cadr term)))
             )
        (if (equal (cadr (cadr term)) ;strip off the quote
                   n)
            (if changed-anything-flg term nil) ;term ;could return the actual value?
          (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n (cadddr term) t))
      (if changed-anything-flg term nil))))

;; (defthm pseudo-termp-of-drop-irrelevant-update-nth-calls-from-update-nth-nest
;;   (implies (pseudo-termp term)
;;            (pseudo-termp (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n term))))

(defthm drop-irrelevant-update-nth-calls-from-update-nth-nest-aux-works-right
  (implies (and (natp n)
                (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n term flg))
           (equal (nth n (nth-update-nth-eval (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n term flg) alist))
                  (nth n (nth-update-nth-eval term alist))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;the function should return a flag if it doesn't do anything and in the case we shouldn't bother to build a new term?  
;takes an nth term
(defun drop-irrelevant-update-nth-calls-from-update-nth-nest (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (consp (caddr term))
           (equal (car (caddr term)) 'update-nth) ;or else don't bother...
           (equal (car term) 'nth)
           (quotep (cadr term))
           (natp (cadr (cadr term)))
           )
      (let ((result (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux
                     (cadr (cadr term)) ;strip off the quote
                     (caddr term)
                     nil)))
        (if result
            `(nth ,(cadr term) 
                  (unhide (hide ,result)))
          term))
    term))

(local (in-theory (disable update-nth)))

(defthm drop-irrelevant-update-nth-calls-from-update-nth-nest-meta-rule
  (equal (nth-update-nth-eval term alist)
         (nth-update-nth-eval (drop-irrelevant-update-nth-calls-from-update-nth-nest term) alist))
  :rule-classes ((:meta :trigger-fns (nth)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;;
;; :meta rule to quickly extract the nth component from a nest of update-nths
;; when the relevant indices are constants
;;

;n is a numeric value
;if this isn't going to make cause any change to the term, just return a flag?
(defun get-nth-component-of-update-nth-nest-aux (n term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term))
      nil
    (if (and (equal 'update-nth (car term))
             (quotep (cadr term))
             (natp (cadr (cadr term)))
             )
        (if (equal (cadr (cadr term)) ;strip off the quote
                   n)
            (caddr term)
          (get-nth-component-of-update-nth-nest-aux n (cadddr term)))
      nil)))

(defthm get-nth-component-of-update-nth-nest-aux-works-right
  (implies (and (get-nth-component-of-update-nth-nest-aux n term)
                (natp n))
           (equal (nth-update-nth-eval (get-nth-component-of-update-nth-nest-aux n term) alist)
                  (nth n (nth-update-nth-eval term alist))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;; (defthm pseudo-termp-of-get-nth-component-of-update-nth-nest
;;   (implies (pseudo-termp term)
;;            (pseudo-termp (get-nth-component-of-update-nth-nest-aux n term))))
  
(defun get-nth-component-of-update-nth-nest (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (consp (caddr term))
           (equal (car (caddr term)) 'update-nth) ;or else don't bother...
           (equal (car term) 'nth)
           (quotep (cadr term))
           (natp (cadr (cadr term)))
           )
      (let* ((val (get-nth-component-of-update-nth-nest-aux
                   (cadr (cadr term)) ;strip off the quote
                   (caddr term))))
        (if val
            `(unhide (hide ,val))
          term))
    term))

(defthm get-nth-component-of-update-nth-nest-meta-rule
  (equal (nth-update-nth-eval term alist)
         (nth-update-nth-eval (get-nth-component-of-update-nth-nest term) alist))
  :rule-classes ((:meta :trigger-fns (nth)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))
