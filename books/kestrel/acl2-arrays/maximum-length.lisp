; A lightweight book about the built-in function maximum-length
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable maximum-length))

(defthm maximum-length-of-cons
  (equal (maximum-length name (cons a x))
         (if (equal :header (car a))
             (cadr (assoc-keyword :maximum-length (cdr a)))
           (maximum-length name x)))
  :hints (("Goal" :in-theory (enable maximum-length header))))

(defthmd normalize-maximum-length-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (maximum-length name l)
                  (maximum-length :fake-name l)))
  :hints (("Goal" :in-theory (enable maximum-length))))

;; We prefer a call to the function MAXIMUM-LENGTH instead of its expanded form,
;; but some functions use the expanded form directly, so we use this rule to
;; convert things into our normal form.
(defthm maximum-length-intro
  (equal (cadr (assoc-keyword :maximum-length (cdr (header name l))))
         (maximum-length name l))
  :hints (("Goal" :in-theory (enable maximum-length))))

(theory-invariant (incompatible (:rewrite maximum-length-intro) (:definition maximum-length)))
