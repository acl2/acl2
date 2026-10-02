; OMP (Orthogonal Matching Pursuit) Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Symbols from books/workshops/2018/kwan-greenstreet/ (vectors.lisp, norm.lisp)
; that are used in the OMP books.  Those books live in the "ACL2" package, so
; we import them by name to make ACL2::vec-+ visible as OMP::vec-+, etc.

(defpkg "OMP"
  (append '(vec-+
            vec--
            vec--x
            scalar-*
            dot
            zvecp
            norm^2
            ; Literate-style documentation and quantified definitions.
            defxdoc+
            std::define-sk)
          ; Drop CL-package symbols we want to redefine in the OMP package.
          (set-difference-eq *std-pkg-symbols*
                             '(vectorp))))
