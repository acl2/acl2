; Lookup a key in an alist using EQ
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains reasoning support for lookup-eq.  Note that we
;; immediately rewrite it to lookup-equal and then reason about that instead.

(include-book "lookup-eq-def")
(include-book "lookup-equal") ;; included becase we rewrite lookup-eq to lookup-equal

;; Our strategy will be to rewrite lookup-eq to lookup-equal.
(defthm lookup-eq-becomes-lookup-equal
  (equal (lookup-eq key alist)
         (lookup-equal key alist))
  :hints (("Goal" :in-theory (enable lookup-equal lookup-eq))))
