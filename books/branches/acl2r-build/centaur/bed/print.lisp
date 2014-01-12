; Centaur BED Library
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>

(in-package "BED")
(include-book "ops")

(define bed-op-name ((x bed-op-p))
  (cond
   ((eql x (bed-op-true)) 'true)
   ((eql x (bed-op-ior))  'or)
   ((eql x (bed-op-orc2)) 'orc2)
   ((eql x (bed-op-arg1)) 'arg1)
   ((eql x (bed-op-orc1)) 'orc1)
   ((eql x (bed-op-arg2)) 'arg2)
   ((eql x (bed-op-eqv))  'eqv)
   ((eql x (bed-op-and))  'and)
   ((eql x (bed-op-nand)) 'nand)
   ((eql x (bed-op-xor))  'xor)
   ((eql x (bed-op-not2)) 'not2)
   ((eql x (bed-op-andc2)) 'andc2)
   ((eql x (bed-op-not1)) 'not1)
   ((eql x (bed-op-andc1)) 'andc1)
   ((eql x (bed-op-nor)) 'nor)
   ((eql x (bed-op-false)) 'false)
   (t 'unknown)))

(define bed-print (x)
  (b* (((when (atom x))
        x)
       ((cons a b) x)
       ((when (atom a))
        (let ((yes (bed-print (car$ b)))
              (no  (bed-print (cdr$ b))))
          (cond ((and (eq yes t)
                      (eq no nil))
                 (list 'VAR a))
                ((and (eq yes nil)
                      (eq no t))
                 (list 'NVAR a))
                (t
                 (list 'VAR-ITE a yes no))))))
    (list (bed-op-name (bed-op-fix b))
          (bed-print (car$ a))
          (bed-print (cdr$ a)))))

