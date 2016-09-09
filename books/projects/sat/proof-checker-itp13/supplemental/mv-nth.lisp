(in-package "PROOF-CHECKER-ITP13")



(defthm mv-nth-0-mv2
   (equal (mv-nth 0 (mv x y))
          x))

(defthm mv-nth-1-mv2
   (equal (mv-nth 1 (mv x y))
          y))


(defthm mv-nth-0-mv3
   (equal (mv-nth 0 (mv x y z))
          x))

(defthm mv-nth-1-mv3
   (equal (mv-nth 1 (mv x y z))
          y))

(defthm mv-nth-2-mv3
   (equal (mv-nth 2 (mv x y z))
          z))

(in-theory (disable mv-nth))
