(in-package "HANOI")

(include-book "misc/records" :dir :system)
(include-book "basic")
(include-book "stack")
(include-book "state")
(include-book "move")


;----------------------------------------------------------------------

(defun do-move (m st)
  (let* ((from (src m))
         (to   (dest m))
         (from-stk (get-peg from st))
         (to-stk   (get-peg to st)))
    (set-peg from 
             (pop from-stk)
             (set-peg to 
                      (push (top from-stk)
                            to-stk)
                      st))))

(defun play (moves s)
  (if (endp moves)
      s
    (play (cdr moves)
          (do-move (car moves) s))))

;----------------------------------------------------------------------
