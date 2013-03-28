; CUTIL - Centaur Basic Utilities
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(ld "package.lsp")
(ld "~/acl2-customization.lsp")
(include-book "portcullis")
(set-deferred-ttag-notes t state)
(set-gag-mode :goals)
(set-inhibit-output-lst '(proof-tree))
(in-package "CUTIL")

(with-output
 :off (summary event)
 (progn

   (defmacro why (rule)
     ;; BOZO eventually improve this to handle other rule-classes and 
     ;; such automatically.  That is, look up the name of the rule, etc.
     `(ACL2::er-progn
       (ACL2::brr t)
       (ACL2::monitor '(:rewrite ,rule) ''(:eval :go t))))

   (include-book "misc/untranslate-patterns" :dir :system)

   (ACL2::add-untranslate-pattern (car ?x) 
                                  (first ?x))

   (ACL2::add-untranslate-pattern (car (car ?x)) 
                                  (first (first ?x)))

   (ACL2::add-untranslate-pattern (car (cdr ?x)) 
                                  (second ?x))

   (ACL2::add-untranslate-pattern (car (car (cdr ?x))) 
                                  (first (second ?x)))

   (ACL2::add-untranslate-pattern (car (cdr (car (cdr ?x))))
                                  (second (second ?x)))

   (ACL2::add-untranslate-pattern (car (cdr (car ?x)))
                                  (second (first ?x)))

   (ACL2::add-untranslate-pattern (car (cdr (cdr ?x))) 
                                  (third ?x))

   (ACL2::add-untranslate-pattern (car (car (cdr (cdr ?x)))) 
                                  (first (third ?x)))

   (ACL2::add-untranslate-pattern (car (cdr (car (cdr (cdr ?x))))) 
                                  (second (third ?x)))

   (ACL2::add-untranslate-pattern (car (cdr (cdr (car (cdr (cdr ?x))))))
                                  (second (third ?x)))

   (ACL2::add-untranslate-pattern (car (cdr (cdr (car (cdr ?x)))))
                                  (third (second ?x)))

   (ACL2::add-untranslate-pattern (car (cdr (cdr (car ?x))))
                                  (third (first ?x)))

   (ACL2::add-untranslate-pattern (car (cdr (cdr (cdr ?x)))) 
                                  (fourth ?x))

   (ACL2::add-untranslate-pattern (car (car (cdr (cdr (cdr ?x))))) 
                                  (first (fourth ?x)))

   (ACL2::add-untranslate-pattern (car (cdr (car (cdr (cdr (cdr ?x))))))
                                  (second (fourth ?x)))

   (ACL2::add-untranslate-pattern (car (cdr (cdr (car (cdr (cdr (cdr ?x)))))))
                                  (third (fourth ?x)))

   (ACL2::add-untranslate-pattern (car (cdr (cdr (cdr (car (cdr (cdr (cdr ?x))))))))
                                  (fourth (fourth ?x)))

   (ACL2::add-untranslate-pattern (car (cdr (cdr (cdr (car (cdr (cdr ?x)))))))
                                  (fourth (third ?x)))

   (ACL2::add-untranslate-pattern (car (cdr (cdr (cdr (car (cdr ?x))))))
                                  (fourth (second ?x)))

   (ACL2::add-untranslate-pattern (car (cdr (cdr (cdr (car ?x)))))
                                  (fourth (first ?x)))

   (ACL2::add-untranslate-pattern (first (cdr ?x))
                                  (second ?x))

   (ACL2::add-untranslate-pattern (first (cdr (cdr ?x)))
                                  (third ?x))

   (ACL2::add-untranslate-pattern (first (cdr (cdr (cdr ?x))))
                                  (fourth ?x))

   (ACL2::optimize-untranslate-patterns)))