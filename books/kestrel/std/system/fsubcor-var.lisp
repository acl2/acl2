; Standard System Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the community-books file 3BSD-mod.txt.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(local (include-book "tools/flag" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm pseudo-termp-of-subcor-var1
   (implies (and (pseudo-term-listp terms)
                 (symbolp var))
            (pseudo-termp (subcor-var1 vars terms var)))))

(local
 (make-flag flag fsubcor-var))

(local
 (defthm len-of-fsubcor-var-lst
   (equal (len (fsubcor-var-lst vars terms forms))
          (len forms))))

(local
 (defthm-flag
   (defthm theorem-for-fsubcor-var
     (implies (and (pseudo-term-listp terms)
                   (pseudo-termp form))
              (pseudo-termp (fsubcor-var vars terms form)))
     :flag fsubcor-var)
   (defthm theorem-for-fsubcor-var-lst
     (implies (and (pseudo-term-listp terms)
                   (pseudo-term-listp forms))
              (pseudo-term-listp (fsubcor-var-lst vars terms forms)))
     :flag fsubcor-var-lst)
   :hints (("Goal" :expand (:free (a b) (pseudo-termp (cons a b)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/system/fsubcor-var
  :parents (std/system/term-transformations)
  :short "Theorems about @(tsee fsubcor-var)."

  (defthm pseudo-termp-of-fsubcor-var
    (implies (and (pseudo-term-listp terms)
                  (pseudo-termp form))
             (pseudo-termp (fsubcor-var vars terms form))))

  (defthm pseudo-term-listp-of-fsubcor-var-lst
    (implies (and (pseudo-term-listp terms)
                  (pseudo-term-listp forms))
             (pseudo-term-listp (fsubcor-var-lst vars terms forms))))

  (defthm len-of-fsubcor-var-lst
    (equal (len (fsubcor-var-lst vars terms forms))
           (len forms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable fsubcor-var fsubcor-var-lst))
