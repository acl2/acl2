(in-package "ACL2")

(include-book "check-equivs")

(local
 (defconst *equiv-alist-for-built-ins*
   (acons 'iff
          (acons 'iff '(iff iff)
                 (acons 'not '(iff)
                        (acons 'implies '(iff iff)
                               nil)))
          (acons 'equal
                 (acons 'iff '(iff iff)
                        (acons 'not '(iff)
                               (acons 'implies '(iff iff)
                                      nil)))
                 nil))))

(local (check-equiv-alist *equiv-alist-for-built-ins*))
