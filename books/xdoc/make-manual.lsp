; XDOC Documentation System for ACL2
; Copyright (C) 2009 Centaur Technology
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
(include-book "top")

(defxdoc subseq
  :short 
  "<p>Subsequence of a string or list</p>"
  :long 
  "@(def subseq)

 <p>This is just an example topic.</p>

 <p>For any natural numbers start and end, where start &lt;=
 end &lt;= (length seq), (subseq seq start end) is the
 subsequence of seq from index start up to, but not including,
 index end.  End may be nil, which which case it is treated
 as though it is (length seq), i.e., we obtain the subsequence of
 seq from index start all the way to the end.</p>


 <p>The guard for (subseq seq start end) is that seq is a
 true list or a string, start and end are integers (except,
 end may be nil, in which case it is treated as (length seq)
 for the rest of this discussion), and 0 &lt;= start &lt;=
 end &lt;= (length seq).</p>
 
 <p>Subseq is a Common Lisp function.  See any Common Lisp
 documentation for more information.  Note:  In Common Lisp the third
 argument of subseq is optional, but in ACL2 it is required,
 though it may be nil as explained above.</p>")

(xdoc::save "manual")
