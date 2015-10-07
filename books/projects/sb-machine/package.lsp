; Copyright (C) 2015, Regents of the University of Texas
; Written by Ben Selfridge
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(include-book "std/portcullis" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)

(defconst *fty-imports*
  '(fty::deflist
    fty::defalist
    fty::defprod
    fty::deftagsum
    fty::deftypes
    fty::deffixtype
    fty::deffixequiv
    fty::deffixequiv-mutual))


(defpkg "SB"
  (union-eq 
   (set-difference-eq
    (union-eq *acl2-exports*
              *common-lisp-symbols-from-main-lisp-package*
              *fty-imports*
              '(std::define
                std::defrule
                std::defruled
                std::b*
                acl2::pm
                acl2::pml))
    `(acl2::prog 
      acl2::program
      acl2::step
      acl2::o-p))))
