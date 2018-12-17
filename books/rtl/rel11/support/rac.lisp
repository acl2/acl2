(in-package "RTL")

(include-book "definitions")

(defthm ash-rewrite
  (equal (ash i c)
         (fl (* (ifix i) (expt 2 c))))
  :hints (("Goal" :in-theory (enable floor fl ash))))
