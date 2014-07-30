#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;bzo the names of the functions below no longer describe what they do?

;The unhide/hide trick is from Robert Krug.
(defun unhide (x)
  (declare (type t x))
  x)

(defthm unhide-hide
  (equal (unhide (hide x))
         x)
  :hints (("Goal" :expand ((hide x)))))

(in-theory (disable unhide))

(defevaluator nth-update-nth-eval nth-update-nth-eval-lst
  ((nth x l)
   (update-nth n v l)
;   (skip-rewrite x)
   (hide x)
   (unhide x)
   ))


;n is a numeric value
;term is a nest of update-nths
;we return a term equivalent to (nth n term), either a value of an nth call on a simpler nest
(defun drop-irrelevant-update-nth-calls-from-update-nth-nest-aux (n term changed-anything-flg)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term))
      (if changed-anything-flg `(nth ',n (unhide (hide ,term))) nil)
    (if (and (equal 'update-nth (car term))
             (quotep (cadr term))
             (natp (cadr (cadr term)))
             )
        (if (equal (cadr (cadr term)) ;strip off the quote
                   n)
            `(unhide (hide ,(caddr term)))
          (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n (cadddr term) t)) ;set the flag
      (if changed-anything-flg `(nth ',n (unhide (hide ,term))) nil))))

;; (defthm pseudo-termp-of-drop-irrelevant-update-nth-calls-from-update-nth-nest
;;   (implies (pseudo-termp term)
;;            (pseudo-termp (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n term))))

(defthm drop-irrelevant-update-nth-calls-from-update-nth-nest-aux-works-right
  (implies (and (natp n)
                (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n nest flg))
           (equal (nth-update-nth-eval (drop-irrelevant-update-nth-calls-from-update-nth-nest-aux n nest flg) alist)
                  (nth n (nth-update-nth-eval nest alist))))
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
            result
          term))
    term))

(local (in-theory (disable update-nth)))

(defthm drop-irrelevant-update-nth-calls-from-update-nth-nest-meta-rule
  (equal (nth-update-nth-eval term alist)
         (nth-update-nth-eval (drop-irrelevant-update-nth-calls-from-update-nth-nest term) alist))
  :rule-classes ((:meta :trigger-fns (nth)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;;tests:
;; (thm (equal (nth 3 (update-nth 2 v (update-nth 3 val2 lst))) VAL2))
;; (thm (equal (nth 3 (update-nth 2 v (update-nth 4 val2 lst))) (nth 3 lst)))
