; ACL2 String Library
; Copyright (C) 2009 Centaur Technology
; Contact: jared@cs.utexas.edu
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

(in-package "ACL2")
(include-book "abbrevs")

:q

;; 10 Million Substrings, 8.1 seconds, nothing allocated
(time (loop for i from 1 to 10000000 do
            (substrp "foo" "this is a string with foo in it")))

;; 10 Million Insensitive Substrings, 13.6 seconds, nothing allocated
(time (loop for i from 1 to 10000000 do
            (isubstrp "foo" "this is a string with foo in it")))

;; 10 Million Reversals, 19.6 seconds, 1.4 GB allocated
(time (loop for i from 1 to 10000000 do
            (reverse "this is a string with foo in it")))

;; 100 Million String< Compares, 5.5 seconds, nothing allocated
(time (loop for i from 1 to 100000000 do
            (string< "this foo" "this bar")))

;; 100 Million Istr< Compares, 15.4 seconds, nothing allocated
(time (loop for i from 1 to 100000000 do
            (istr< "this foo" "this bar")))


(defparameter *foo* 
  (loop for i from 1 to 1000 nconc
        (list "foo" "bar" "baz")))

;; 1000 insensitive 3000-element string sort, 6.7 seconds, 500 MB allocated
(time (loop for i from 1 to 1000 do
            (istrsort *foo*)))



