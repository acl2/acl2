; Butlast lemmas
; Copyright (C) 2005-2013 by Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
;
; butlast.lisp

(in-package "ACL2")
(local (include-book "take"))
(local (include-book "arithmetic/top" :dir :system))

(defthm butlast-redefinition
  (equal (butlast x n)
         (if (>= (nfix n) (len x))
             nil
           (cons (car x)
                 (butlast (cdr x) n))))
  :rule-classes ((:definition :clique (butlast)
                  :controller-alist ((butlast t t)))))

(defun butlast-induction (x n)
  (if (>= (nfix n) (len x))
      nil
    (cons (car x)
          (butlast-induction (cdr x) n))))

(defthm use-butlast-induction
  t
  :rule-classes ((:induction
                  :pattern (butlast x n)
                  :scheme (butlast-induction x n))))

  


