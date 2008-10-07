


(in-package "ACL2")

(defun before-arithmetic () nil)

(table pre-arith4-theory-invariants nil
       (table-alist 'theory-invariant-table world)
       :clear)

(include-book "arithmetic-4/top" :dir :system)
(include-book "tools/rulesets" :dir :system)

(def-ruleset! arith4-enable-ruleset (set-difference-theories
                                     (current-theory :here)
                                     (current-theory
                                      'before-arithmetic)))

(def-ruleset! arith4-disable-ruleset (set-difference-theories
                                      (current-theory 'before-arithmetic)
                                      (current-theory :here)))


(table post-arith4-theory-invariants nil
       (table-alist 'theory-invariant-table world)
       :clear)

(table theory-invariant-table nil
       (table-alist 'pre-arith4-theory-invariants world)
       :clear)

(in-theory (e/d* () ((:ruleset arith4-enable-ruleset))
                 ((:ruleset arith4-disable-ruleset))))

