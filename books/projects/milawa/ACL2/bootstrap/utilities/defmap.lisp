; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "utilities")
(%interactive)

(defun %defmap-fn (map key val key-list val-list val-of-nil)
  (declare (xargs :mode :program))
  (let ((mapp (car map))
        (keyp (car key))
        (valp (car val))
        (key-listp (car key-list))
        (val-listp (car val-list))
        ;(map-formals (cdr map))
        ;(key-formals (cdr key))
        ;(val-formals (cdr val))
        ;(key-list-formals (cdr key-list))
        ;(val-list-formals (cdr val-list))
        )
    `(defsection ,mapp

       (local (%forcingp nil))

       (%autoadmit ,mapp)

       (%autoprove ,(ACL2::mksym mapp '-when-not-consp)
                   (%restrict default ,mapp (equal x 'x)))

       (%autoprove ,(ACL2::mksym mapp '-of-cons)
                   (%restrict default ,mapp (equal x '(cons a x))))

       (%autoprove ,(ACL2::mksym 'consp-when-memberp-of- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym 'consp-when-memberp-of- mapp '-alt))

       (local (%disable default
                        ,(ACL2::mksym 'consp-when-memberp-of- mapp)
                        ,(ACL2::mksym 'consp-when-memberp-of- mapp '-alt)))

       (%autoprove ,(ACL2::mksym keyp '-of-car-when-memberp-of- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym keyp '-when-lookup-in- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym valp '-of-cdr-when-memberp-of- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym 'booleanp-of- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym mapp '-of-list-fix)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym mapp '-of-app)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym mapp '-of-rev)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym mapp '-of-remove-all-when- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym mapp '-of-remove-duplicates)
                   (%cdr-induction x)
                   (%enable default ,(ACL2::mksym 'consp-when-memberp-of- mapp)))

       (%autoprove ,(ACL2::mksym mapp '-of-difference-when- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym mapp '-of-subset-when- mapp)
                   (%cdr-induction x)
                   (%enable default ,(ACL2::mksym 'consp-when-memberp-of- mapp)))

       (%autoprove ,(ACL2::mksym mapp '-of-subset-when- mapp '-alt))

       ,@(if (not key-list)
             nil
           `((%autoprove ,(ACL2::mksym key-listp '-of-domain-when- mapp)
                         (%cdr-induction x))))

       ,@(if (not val-list)
             nil
           `((%autoprove ,(ACL2::mksym val-listp '-of-range-when- mapp)
                         (%cdr-induction x))))

       (%autoprove ,(ACL2::mksym 'mapp-when- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym valp '-of-cdr-of-lookup-when- mapp)
                   (%cdr-induction x))

       ,@(if val-of-nil
             nil
           `((%autoprove ,(ACL2::mksym 'cdr-of-lookup-under-iff-when- mapp)
                         (%use (%instance (%thm ,(ACL2::mksym valp '-of-cdr-of-lookup-when- mapp))))
                         (%disable default ,(ACL2::mksym valp '-of-cdr-of-lookup-when- mapp)))))

       )))

(defmacro %defmap (&key map key val key-list val-list (val-of-nil 't))
  (declare (xargs :guard (and (ACL2::symbol-listp map)
                              (ACL2::symbol-listp key)
                              (ACL2::symbol-listp val)
                              (ACL2::symbol-listp key-list)
                              (ACL2::symbol-listp val-list)
                              (consp map)
                              (consp key)
                              (consp val)
                              (or (consp key-list) (not key-list))
                              (or (consp val-list) (not val-list))
                              ;; Argument lists must all be unique
                              (uniquep (cdr map))
                              (uniquep (cdr key))
                              (uniquep (cdr val))
                              (uniquep (cdr key-list))
                              (uniquep (cdr val-list))
                              ;; Argument lists must contain only the names in
                              ;; the map formals
                              (subsetp (cdr key) (cdr map))
                              (subsetp (cdr val) (cdr map))
                              (or (not key-list)
                                  (subsetp (cdr key-list) (cdr map)))
                              (or (not val-list)
                                  (subsetp (cdr val-list) (cdr map)))
                              ;; x must be in each argument list
                              ;; a,b must not be found in any argument list
                              (memberp 'x (cdr map))
                              (not (memberp 'a (cdr map)))
                              (not (memberp 'y (cdr map))))))
  (%defmap-fn map key val key-list val-list val-of-nil))
