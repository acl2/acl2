; VL Verilog Toolkit
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

(defmacro cwtime (form &key name (mintime 'nil) (minalloc 'nil))
  "Concise time reports with optional names."
  (let ((name (or name
                  (and (consp form)
                       (symbolp (car form))
                       (car form))
                  'cwtime)))
    `(time$ ,form
            :msg "; ~s0: ~st seconds, ~sa bytes.~%"
            :args (list ',name)
            :mintime ,mintime
            :minalloc ,minalloc)))

(defmacro xf-cwtime (form &key
                          name
                          (mintime '1)
                          ;; 64 MB minalloc to report
                          (minalloc '67108864))
  "Same as cwtime, but defaults to 1sec / 64 MB alloc minimum.  This is nice as
a sort of passive performance monitor: if everything is running quickly you
won't be bothered with timing info, but if something is taking awhile or a lot
of memory, you'll get a chance to notice it."
  `(cwtime ,form
           :name ,name
           :mintime ,mintime
           :minalloc ,minalloc))

#||

(cwtime (append '(1 2 3) '(4 5 6)))
(cwtime (+ 1 2))
(cwtime 3)

||#

