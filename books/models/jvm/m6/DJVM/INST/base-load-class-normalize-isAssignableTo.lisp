(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")
(include-book "base-valid-type-s")

(local (include-book "base-load-class-normalize-isAssignableTo-support"))

(defthm isAssignableTo-isAssignableTo-resolveClassReference
  (implies (and (car (isAssignableTo typ1 typ2 s))
                (valid-type-strong typ1 (instance-class-table s))
                (consistent-state s)
                (no-fatal-error? (resolveClassReference any s)))
           (car (isAssignableTo typ1 typ2 (resolveClassReference any s))))
  :hints (("Goal" :do-not '(generalize)
           :cases ((no-fatal-error? s)))))

(in-theory (disable isAssignableTo))

