; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "std/util/defrule" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection arithmetic-theorems
  :parents (library-extensions)
  :short "Some theorems about arithmetic."

  (defruled evenp-of-1-less-when-not-evenp
    (implies (and (integerp x)
                  (not (evenp x)))
             (evenp (1- x)))
    :enable evenp)

  (defruled evenp-of-3-less-when-not-evenp
    (implies (and (integerp x)
                  (not (evenp x)))
             (evenp (- x 3)))
    :enable evenp)

  (defruled lt-to-2+le-when-both-evenp
    (implies (and (rationalp x)
                  (rationalp y)
                  (evenp x)
                  (evenp y))
             (equal (< x y)
                    (<= (+ 2 x) y)))
    :instructions
    ((s-prop)
     (prove :hints (("Goal" :in-theory (enable evenp)))))))
