; Standard System Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fsublis-var")

(include-book "std/typed-alists/symbol-pseudoterm-alistp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection fsublis-var-ext
  :extension fsublis-var

  (defthmd pseudo-termp-of-fsublis-var-when-symbol-pseudoterm-alistp
    (implies (and (symbol-pseudoterm-alistp alist)
                  (pseudo-termp term))
             (pseudo-termp (fsublis-var alist term)))
    :hints (("Goal" :in-theory (enable symbol-pseudoterm-alistp-alt-def))))

  (defthmd pseudo-term-listp-of-fsublis-var-lst-when-symbol-pseudoterm-alistp
    (implies (and (symbol-pseudoterm-alistp alist)
                  (pseudo-term-listp terms))
             (pseudo-term-listp (fsublis-var-lst alist terms)))
    :hints (("Goal" :in-theory (enable symbol-pseudoterm-alistp-alt-def)))))
