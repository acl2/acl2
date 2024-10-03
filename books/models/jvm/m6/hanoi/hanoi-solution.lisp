(in-package "HANOI")

(include-book "hanoi-model")

;----------------------------------------------------------------------

;; (defun do-move (m st)
;;   (let* ((from (src m))
;;          (to   (dest m))
;;          (from-stk (get-peg from st))
;;          (to-stk   (get-peg to st)))
;;     (set-peg from 
;;              (pop from-stk)
;;              (set-peg to 
;;                       (push (top from-stk)
;;                             to-stk)
;;                       st))))

;----------------------------------------------------------------------

(defun play-hanoi (from to temp n st)
  (if (zp n) st
    (let* ((st1 (play-hanoi from temp to (- n 1) st))
           (st2 (do-move (new-move from to) st1))
           (st3 (play-hanoi temp to from (- n 1) st2)))
      st3)))

;----------------------------------------------------------------------

(defun h (from to temp n)
  (if (zp n) nil
    (app (h from temp to (- n 1))
         (cons (new-move from to)
               (h temp to from (- n 1))))))

(defun Hanoi (n)
  (h 'A 'B 'C n)) 
  
(defun tower (n)
   (if (zp n)
       nil
     (app (tower (- n 1)) (list n))))

    
(defun init-state (n)
  (s 'A (tower n)
     (s 'B nil 
        (s 'C nil nil))))

(defun final-state (n)
  (s 'A nil
     (s 'B (tower n)
        (s 'C nil nil))))

(defthm examples
  (equal (play (Hanoi 7) (init-state 7))
         (final-state 7)))





;----------------------------------------------------------------------

(defun big-tops (a b c s n)
  (let ((a-stk (g a s))
        (b-stk (g b s))
        (c-stk (g c s)))
    (and (or (not (has-morep a-stk))
             (< n (top a-stk)))
         (or (not (has-morep b-stk))
             (< n (top b-stk)))
         (or (not (has-morep c-stk))
             (< n (top c-stk))))))
       
;----------------------------------------------------------------------
(defun induction-hint (from to temp n s)
  (if (zp n)
      (list from to temp n s)
    (list (induction-hint from temp to (- n 1) 
                          (s from (push n (g from s)) s))
          (induction-hint temp to from (- n 1)
                          (s to (push n (g to s)) s)))))

;----------------------------------------------------------------------

(defthm play-app
  (equal (play (app a b) s)
         (play b (play a s))))


(defthm app2-list
  (equal (APP (APP l (LIST n))
              l1)
         (app l (push n l1)))
  :hints (("Goal" 
           :do-not '(generalize)
           :in-theory (enable push))))

(defthm pop-push
  (equal (pop (push n l))
         l)
  :hints (("Goal" :in-theory (enable push pop))))

(defthm top-push
  (equal (top (push n l))
         n)
  :hints (("Goal" :in-theory (enable push top))))

(defthm s-from-g-from-no-change
  (implies (equal (g from s2) x)
           (equal (S FROM x s2)
                  s2)))
         
(defthmd h-lemma
  (implies (and (natp n)
                (pegp from)
                (pegp to)
                (pegp temp)
                (not (equal from to))
                (not (equal from temp))
                (not (equal to temp))
                (big-tops from to temp s n))
           (equal (play (h from to temp n)
                        (s from (app (tower n)
                                     (g from s)) s))
                  (s to (app (tower n)
                             (g to s)) s)))
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (enable new-move)
           :induct (induction-hint from to temp n s))))

;----------------------------------------------------------------------

(defthm app-nil
  (implies (true-listp l)
           (equal (app l nil) l)))

(defthm true-listp-tower-n
  (true-listp (tower n)))

;----------------------------------------------------------------------

;; functional specification 

(defthm hanoi-correct
  (equal (play (Hanoi n) (init-state n))
         (final-state n))
  :hints (("Goal" 
           :use (:instance h-lemma
                           (from  'A)
                           (to    'B)
                           (temp  'C)
                           (s     nil)))))

;----------------------------------------------------------------------
