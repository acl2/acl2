(in-package "*")

(encapsulate ; Input declarations.
 ((in () t)
  (longop () t))
 (local (defun in () 0))
 (local (defun longop () 0))
 (defthm acl2::input-spec-thm
   (and (bvecp (in) 4)
        (bvecp (longop) 1))
   :rule-classes ()))
