(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")

(local (include-book "base-consistent-state-pushCategory2-support"))

(DEFTHM
  CONSISTENT-STATE-PUSHSTACK-CONSISTENT-STATE-PUSHSTACK-2
  (IMPLIES (AND (CONSISTENT-VALUE-X V (INSTANCE-CLASS-TABLE S)
                                    (HEAP S))
                (CATEGORY2 V)
                (<= (+ 2
                       (LEN (OPERAND-STACK (CURRENT-FRAME S))))
                    (MAX-STACK S))
                (CONSISTENT-STATE S))
           (CONSISTENT-STATE (PUSHSTACK V (pushStack '(topx . topx) S)))))





