; Doublets
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection doublets-to-alist
  :parents (kestrel-utilities system-utilities)
  :short "Turn a true list of doublets
          (i.e. lists of length 2)
          into the corresponding alist."
  :long
  "<p>
   This is the inverse of
   <see topic='@(url system-utilities)'>@('alist-to-doublets')</see>.
   </p>"

  (defun doublets-to-alist (doublets)
    (declare (xargs :guard (doublet-listp doublets)))
    (if (endp doublets)
        nil
      (cons (cons (car (first doublets)) (cadr (first doublets)))
            (doublets-to-alist (rest doublets)))))

  (defthm doublets-to-alist-of-alist-to-doublets
    (implies (alistp x)
             (equal (doublets-to-alist (alist-to-doublets x))
                    x)))

  (defthm alist-to-doublets-of-doublets-to-alist
    (implies (doublet-listp x)
             (equal (alist-to-doublets (doublets-to-alist x))
                    x))))
