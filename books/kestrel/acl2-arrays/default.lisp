; A lightweight book about the built-in function default
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable default))

;; We prefer a call to the function DEFAULT instead of its expanded form,
;; but some functions use the expanded form directly, so we use this rule to
;; convert things into our normal form.
(defthm default-intro
  (equal (cadr (assoc-keyword :default (cdr (header name l))))
         (default name l))
  :hints (("Goal" :in-theory (enable default))))

(theory-invariant (incompatible (:rewrite default-intro) (:definition default)))

;; This one also collapses the call to header
;; Unfortunately, this has a free variable in the RHS.
(defthmd default-intro2
  (equal (cadr (assoc-keyword :default (cdr (ASSOC-EQUAL :HEADER L))))
         (default name l))
  :hints (("Goal" :in-theory (e/d (default header) (default-intro)))))

(theory-invariant (incompatible (:rewrite default-intro2) (:definition default)))

(defthm default-of-nil
  (equal (default name nil)
         nil)
  :hints (("Goal" :in-theory (e/d (default) (default-intro)))))

(defthm default-of-cons
  (equal (default name (cons a x))
         (if (equal :header (car a))
             (cadr (assoc-keyword :default (cdr a)))
           (default name x)))
  :hints (("Goal" :in-theory (e/d (default header) (default-intro)))))
