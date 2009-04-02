;; Processing Unicode Files with ACL2
;; Copyright (C) 2005-2006 by Jared Davis <jared@cs.utexas.edu>
;;
;; This program is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2 of the License, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along with
;; this program; if not, write to the Free Software Foundation, Inc., 59 Temple
;; Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")

(local (defthm intern-in-package-of-symbol-lemma
         (implies (and (stringp a)
                       (stringp b)
                       (symbolp in-pkg)
                       (not (equal a b)))
                  (not (equal (intern-in-package-of-symbol a in-pkg)
                              (intern-in-package-of-symbol b in-pkg))))
         :hints(("Goal" 
                 :use ((:instance symbol-name-intern-in-package-of-symbol
                                  (s a) (any-symbol in-pkg))
                       (:instance symbol-name-intern-in-package-of-symbol
                                  (s b) (any-symbol in-pkg)))))))

(defthm equal-of-intern-in-package-of-symbols
  (implies (and (stringp a)
                (stringp b)
                (symbolp in-pkg))
           (equal (equal (intern-in-package-of-symbol a in-pkg)
                         (intern-in-package-of-symbol b in-pkg))
                  (equal a b))))