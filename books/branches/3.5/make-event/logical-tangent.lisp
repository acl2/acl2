; Copyright (C) 2006  University of Texas at Austin

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; By Peter Dillinger
;
; Here I use make-event to define a macro LOGICAL-TANGENT, which behaves
; a bit like WORMHOLE, but is a bit different.  WORMHOLE provides an LD
; environment in which all STATE changes are reverted after it finishes.
; LOGICAL-TANGENT provides and LD environment in which changes to the WORLD
; and other settings (in *protected-state-globals-for-make-event*) are
; reverted after it finishes.  WORMHOLE is logically meaningless.
; LOGICAL-TANGENT takes state (under the hood) and returns a passing
; "error triple".  LOGICAL-TANGENT doesn't need the special "tunneling"
; capability of wormholes, as user-defined state globals and stobjs are
; not reverted.

(in-package "ACL2")

(defmacro logical-tangent ()
  '((lambda () ; to make this invalid as an embedded event form
      (make-event
       (mv-let (erp val state)
               (ld (standard-oi state)
                   :ld-error-action (ld-error-action state))
               (declare (ignore erp val))
               (value '(value-triple :invisible)))))))
