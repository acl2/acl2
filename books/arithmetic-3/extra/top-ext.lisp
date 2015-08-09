; Arithmetic-3 Extensions
; See the top-level arithmetic-3 LICENSE file for copyright and license information.
; Contributed 2006 by Alex Spiridonov, with helpful consulting from Robert Krug.

(in-package "ACL2")

(include-book "arithmetic-3/bind-free/top" :dir :system)
(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)
(include-book "ext")

(add-default-hints! '((nonlinearp-default-hint stable-under-simplificationp
                                               hist pspv)))

(in-theory (enable strong-expt-type-prescription-rules))
