(in-package "DJVM")
(include-book "base")

(skip-proofs 
 (defthm frame-sig-update-heap
   (implies (and (REFp v hp)
                 (not (NULLp v))
                 (equal (obj-type new-obj) (obj-type (deref2 v hp))))
            (equal (frame-sig frame cl (bind (rREF v) new-obj hp) hp-init)
                   (frame-sig frame cl hp hp-init)))))