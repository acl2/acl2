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

(include-book "utf8-decode-char")


























(defthm utf8-table36-okp-when-not-expected-length
  (implies (not (equal (utf8-table35-expected-length (first x))
                       (len x)))
           (not (utf8-table36-ok? cp x)))
  :hints(("Goal" :in-theory (enable utf8-table36-ok?
                                    utf8-table35-byte-1/1?
                                    utf8-table35-byte-1/2?
                                    utf8-table35-byte-1/3?
                                    utf8-table35-byte-1/4?
                                    utf8-table35-trailing-byte?
                                    utf8-table36-rows
                                    utf8-table36-codepoint-1?
                                    utf8-table36-codepoint-2?
                                    utf8-table36-codepoint-3?
                                    utf8-table36-codepoint-4?
                                    utf8-table36-codepoint-5?
                                    utf8-table36-codepoint-6?
                                    utf8-table36-codepoint-7?
                                    utf8-table36-codepoint-8?
                                    utf8-table36-codepoint-9?
                                    utf8-table36-bytes-1?
                                    utf8-table36-bytes-2?
                                    utf8-table36-bytes-3?
                                    utf8-table36-bytes-4?
                                    utf8-table36-bytes-5?
                                    utf8-table36-bytes-6?
                                    utf8-table36-bytes-7?
                                    utf8-table36-bytes-8?
                                    utf8-table36-bytes-9?
                                    utf8-table35-expected-length))))

(defthm utf8-table35-expected-length-when-utf8-table36-ok?
  (implies (utf8-table36-ok? cp x)
           (equal (utf8-table35-expected-length (first x))
                  (len x))))
