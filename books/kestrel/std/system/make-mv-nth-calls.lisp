; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-mv-nth-calls ((term pseudo-termp) (n natp))
  :returns (terms pseudo-term-listp :hyp (pseudo-termp term))
  :parents (std/system/term-transformations)
  :short "Given a term @('term'), return the list of @('n') terms
          @('((mv-th '0 term) ... (mv-nth 'n-1 term))')."
  (make-mv-nth-calls-aux term 0 n)

  :prepwork
  ((define make-mv-nth-calls-aux ((term pseudo-termp) (i natp) (n natp))
     :returns (terms pseudo-term-listp :hyp (pseudo-termp term))
     (if (or (not (mbt (natp i)))
             (not (mbt (natp n)))
             (>= i n))
         nil
       (cons `(mv-nth ',i ,term)
             (make-mv-nth-calls-aux term (1+ i) n)))
     :measure (nfix (- n i))
     ///
     (defret len-of-make-mv-nth-calls-aux
       (equal (len terms)
              (if (natp i)
                  (nfix (- (nfix n) i))
                0)))))

  ///

  (defret len-of-make-mv-nth-calls
    (equal (len terms)
           (nfix n))))
