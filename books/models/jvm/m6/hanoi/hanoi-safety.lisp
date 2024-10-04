(in-package "HANOI")

(include-book "state")
(include-book "move")
(include-book "hanoi-model")
(include-book "hanoi-solution")
(include-book "perm")

;; (defun disks-perm (st l)
;;   (perm (app (get-peg 'A st) 
;;              (app (get-peg 'B st)
;;                   (get-peg 'C st)))
;;         l))

(defun disks-perm (st l)
   (perm (app (get-peg 'A st) 
              (app (get-peg 'B st)
                   (get-peg 'C st)))
         l))

;----------------------------------------------------------------------

(defund wff-move (m) 
   (and (movep m)
        (not (equal (src m)
                    (dest m)))))

(defund legal-movep1 (m s)
  (let ((from-stk (get-peg (src m) s)))
    (and (wff-move m)
         (has-morep from-stk))))

;----------------------------------------------------------------------

(defthmd do-move-preserve-disk-perm
     (implies (and (legal-movep1 m st)
                   (disks-perm st l))
              (disks-perm (do-move m st) l))
     :hints (("Goal" :in-theory (e/d (push top pop
                                           has-morep
                                           wff-move 
                                           movep
                                           pegp
                                           perm-app-cons-norm-1
                                           perm-app-cons-norm-0
                                           legal-movep1
                                           perm-app-reduce-1
                                           perm-app-reduce-2)
                                     (perm)))))

;----------------------------------------------------------------------

(defun stack-inorder (stk) 
  (declare (xargs :hints (("Goal" :in-theory (enable has-morep pop push)))))
  (if (has-morep stk)
      (if (has-morep (pop stk))
          (and (< (top stk) 
                  (top (pop stk)))
               (stack-inorder (pop stk)))
        t)
    t))


(defund disks-inorder (st)
  (and (stack-inorder (g 'A st))
       (stack-inorder (g 'B st))
       (stack-inorder (g 'C st))))

(defund legal-movep2 (m s)
  (let ((from-stk (get-peg  (src m) s))
        (to-stk (get-peg (dest m) s)))
    (and (wff-move m)
         (has-morep from-stk)
         (or (not (has-morep to-stk))
             (< (top from-stk)
                (top to-stk))))))

;----------------------------------------------------------------------

(defthmd do-move-preserve-disks-inorder
     (implies (and (legal-movep2 m st)
                   (disks-inorder st))
              (disks-inorder (do-move m st)))
     :hints (("Goal" :in-theory (e/d (push top pop
                                           has-morep
                                           disks-inorder
                                           wff-move 
                                           movep
                                           pegp
                                           legal-movep2)
                                     ()))))


;----------------------------------------------------------------------

(defun safe-state (st n)
  (and (disks-perm st (tower n))
       (disks-inorder st)))


(defund legal-movep (m s)
  (and (legal-movep1 m s)
       (legal-movep2 m s)))



(defthmd do-move-preserve-safe-state
     (implies (and (legal-movep m st)
                   (safe-state st n))
              (safe-state (do-move m st) n))
     :hints (("Goal" :in-theory (e/d (legal-movep 
                                      safe-state
                                      do-move-preserve-disk-perm
                                      do-move-preserve-disks-inorder)
                                     (do-move disks-perm disks-inorder)))))


;----------------------------------------------------------------------


(defun safe-moves (moves s)
  (if (endp moves)
      t
    (and (legal-movep (car moves) s)
         (safe-moves (cdr moves)
                     (do-move (car moves) s)))))


(defthm safe-moves-app
  (implies (safe-moves a s)
           (equal (safe-moves (app a b) s)
                  (safe-moves b (play a s)))))


;----------------------------------------------------------------------

(defthm safe-moves-preserve-safe-state
  (implies (and (safe-state st n)
                (safe-moves moves st))
           (safe-state (play moves st) n))
  :hints (("Goal" :in-theory (e/d (do-move-preserve-safe-state)
                                  (safe-state do-move)))))

(local 
(defthmd h-lemma-2
  (implies (and (natp n)
                (pegp from)
                (pegp to)
                (pegp temp)
                (not (equal from to))
                (not (equal from temp))
                (not (equal to temp))
                (big-tops from to temp (s from anylist s) n))
           (equal (play (h from to temp n)
                        (s from (app (tower n) anylist) s))
                  (s from anylist 
                     (s to (app (tower n)
                                (g to s)) s))))
  :hints (("Goal" :use ((:instance h-lemma
                                   (s (s from anylist s))))))))


(local
(defthmd h-is-safe-lemma
   (implies (and (natp n)
                 (pegp from)
                 (pegp to)
                 (pegp temp)
                 (not (equal from to))
                 (not (equal from temp))
                 (not (equal to temp))
                 (big-tops from to temp s n))
            (safe-moves (h from to temp n)
                        (s from (app (tower n)
                                     (g from s)) s))) 
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (enable wff-move has-morep 
                              legal-movep h-lemma-2
                              h-lemma new-move movep
                              legal-movep1 legal-movep2)
           :induct (induction-hint from to temp n s)))))

;----------------------------------------------------------------------

(defthm safe-play
  (safe-moves (Hanoi n) (init-state n))
  :hints (("Goal" :use ((:instance h-is-safe-lemma
                                   (from 'A)
                                   (to 'B)
                                   (temp 'C)
                                   (s nil))))))
;----------------------------------------------------------------------

(defun collect-states (moves st)
  (if (endp moves)
      nil
    (let ((nx-state (do-move (car moves) st)))
      (cons nx-state (collect-states (cdr moves) nx-state)))))


(defun all-safe-states (stl n)
  (if (endp stl) t
    (and (safe-state (car stl) n)
         (all-safe-states (cdr stl) n))))


(defthm safe-moves-implies-safe-state
  (implies (and (safe-moves moves st)
                (safe-state st n))
           (all-safe-states (collect-states moves st) n))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (do-move-preserve-safe-state)
                           (safe-state legal-movep do-move)))))

;----------------------------------------------------------------------
(defthm stack-inorder-app
  (implies (and (stack-inorder stk)
                (case-split (consp stk))
                (case-split (< (car (last stk)) n)))
           (stack-inorder (app stk (list n))))
  :hints (("Goal" :in-theory (e/d (stack-inorder
                                   pop push top has-morep)
                                  ()))))

(defthm stack-inorder-list-n
  (stack-inorder (list n))
  :hints (("Goal" :in-theory (enable has-morep pop top 
                                     stack-inorder))))


;; (defthm stack-inorder-app-2
;;   (implies (and (stack-inorder stk)
;;                 (not (consp stk))
;;            (stack-inorder (app stk (list n))))
;;   :hints (("Goal" :in-theory (e/d (stack-inorder
;;                                    pop push top has-morep)
;;                                   ()))))

(defthm last-app
  (equal  (car (last (app l (list n))))
          n))

(defthm last-tower-n
  (implies (and (natp n)
                (case-split (> n 0)))
           (equal (car (last (tower n))) n))
  :hints (("Goal" :in-theory (enable tower))))

(defthm consp-tower-n
  (implies (natp n)
           (iff (consp (tower n))
                (> n 0))))
                


(defthm stack-inorder-tower-n
  (implies (natp n)
           (stack-inorder (tower n)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (stack-inorder
                            pop push top has-morep)
                           ()))))

(defthm safe-state-init-state
  (safe-state (init-state n) n)
  :hints (("Goal" :in-theory (enable disks-inorder stack-inorder))))


(defthm safe-play-1
  (all-safe-states (collect-states (Hanoi n) (init-state n)) n)
  :hints (("Goal" :in-theory (e/d () (Hanoi init-state)))))

;----------------------------------------------------------------------
