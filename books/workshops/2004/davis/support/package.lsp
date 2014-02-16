#|

   Fully Ordered Finite Sets, Version 0.9
   Copyright (C) 2003, 2004 by Jared Davis <jared@cs.utexas.edu>

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public Lic-
   ense along with this program; if not, write to the Free Soft-
   ware Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
   02111-1307, USA.
 


  package.lisp

    Defpackage events for the set theory library.

|#


(defpkg "INSTANCE"
  (union-eq '()
    (union-eq *acl2-exports*
  	      *common-lisp-symbols-from-main-lisp-package*)))


(defpkg "COMPUTED-HINTS"
  (union-eq '(mfc-ancestors 
	      mfc-clause
	      string-for-tilde-@-clause-id-phrase
	      INSTANCE::instance-rewrite)
    (union-eq *acl2-exports*
  	      *common-lisp-symbols-from-main-lisp-package*)))


(defpkg "SET"
  (set-difference-equal (union-eq '(lexorder
				    COMPUTED-HINTS::rewriting-goal-lit
				    COMPUTED-HINTS::rewriting-conc-lit)
                          (union-eq *acl2-exports*
                            *common-lisp-symbols-from-main-lisp-package*))
                        '(union delete find map)))

