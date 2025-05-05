(include-book "acl2s/interface/acl2s-utils/top" :dir :system)
:q

(load "../try-load-quicklisp.lisp")
(pushnew (truename "../../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-lengths
  (:use :cl :z3 :acl2s :acl2s-interface))

(in-package :z3-lengths)
(import 'acl2s-interface::acl2s-compute)
(import 'acl2s-interface-extras::itest?-query)

;; When we ask ACL2s, we don't get any counterexamples...
(itest?-query
 (let ((*package* (find-package 'acl2s)))
   (read-from-string
    "(implies (and (intp x) (intp y) (intp z) (intp a) (intp b)
                         (< x 100)
                         (< y 100)
                         (< z 100)
                         (< a 100)
                         (< b 100))
                (not (> (+ x y z a b) 490)))")))

;; What if we ask Z3?
(solver-init)
(z3-assert
 (x :int y :int z :int a :int b :int)
 (and (< x 100)
      (< y 100)
      (< z 100)
      (< a 100)
      (< b 100)
      (> (+ x y z a b) 490)))
(check-sat)
(get-model)

;; Just to double check, let's evaluate this in ACL2s
(acl2s-compute `(let ,(get-model-as-assignment)
                  (and (< x 100)
                       (< y 100)
                       (< z 100)
                       (< a 100)
                       (< b 100)
                       (> (+ x y z a b) 490))))
;; We get (NIL T), indicating that the above returns `T` and no error
;; occurred during evaluation.

