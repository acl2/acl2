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

(defun %deflist-fn (name formals element negatedp hintsmap)
  (declare (xargs :mode :program))
  (and (or (ACL2::symbolp name)
           (ACL2::er ACL2::hard '%deflist
                     "Name must be a symbol, but is ~x0.~%" name))
       (or (and (ACL2::symbol-listp formals)
                (uniquep formals)
                (memberp 'x formals))
           (ACL2::er ACL2::hard '%deflist
                     "The formals must be a list of unique symbols which ~
                      contain x, but the formals are ~x0.~%" formals))
       (or (and (not (memberp 'y formals))
                (not (memberp 'a formals)))
           (ACL2::er ACL2::hard '%deflist
                     "As a special restriction, formals may not mention a, n, or ~
                      y, but the formals are ~x0.~%" formals))
       (or (and (ACL2::symbolp (car element))
                (consp element))
           (ACL2::er ACL2::hard '%deflist
                     "The element transformation must be a function applied ~
                      to the formals, but is ~x0.~%" element))
       (or (booleanp negatedp)
           (ACL2::er ACL2::hard '%deflist
                     ":negatedp must be a boolean, but is ~x0.~%" negatedp))
       (or (mapp hintsmap)
           (ACL2::er ACL2::hard '%deflist
                     ":hintsmap must be an alist, but is ~x0.~%" hintsmap))
       (let ((elementp (car element)))

         `(defsection ,(ACL2::mksym name '-deflist)

            (local (%forcingp nil))

            (ACL2::make-event (if (tactic.find-rule ',name
                                                    (tactic.harness->world (ACL2::w ACL2::state)))
                                  '(ACL2::value-triple :redundant)
                                '(%autoadmit ,name)))

            (ACL2::make-event (if (tactic.find-rule ',(ACL2::mksym name '-when-not-consp)
                                                    (tactic.harness->world (ACL2::w ACL2::state)))
                                  '(ACL2::value-triple :redundant)
                                '(%autoprove ,(ACL2::mksym name '-when-not-consp)
                                             ,@(or (cdr (lookup (ACL2::mksym name '-when-not-consp) hintsmap))
                                                   `((%restrict default ,name (equal x 'x)))))))
            (local (%enable default ,(ACL2::mksym name '-when-not-consp)))

            (ACL2::make-event (if (tactic.find-rule ',(ACL2::mksym name '-of-cons)
                                                    (tactic.harness->world (ACL2::w ACL2::state)))
                                  '(ACL2::value-triple :redundant)
                                '(%autoprove ,(ACL2::mksym name '-of-cons)
                                             ,@(or (cdr (lookup (ACL2::mksym name '-of-cons) hintsmap))
                                                   `((%restrict default ,name (equal x '(cons a x))))))))
            (local (%enable default ,(ACL2::mksym name '-of-cons)))

            (ACL2::make-event (if (tactic.find-rule ',(ACL2::mksym 'booleanp-of- name)
                                                    (tactic.harness->world (ACL2::w ACL2::state)))
                                  '(ACL2::value-triple :redundant)
                                '(%autoprove ,(ACL2::mksym 'booleanp-of- name)
                                             ,@(or (cdr (lookup (ACL2::mksym 'booleanp-of- name) hintsmap))
                                                   `((%cdr-induction x))))))
            (local (%enable default ,(ACL2::mksym 'booleanp-of- name)))

            (%autoprove ,(ACL2::mksym name '-of-list-fix)
                        ,@(or (cdr (lookup (ACL2::mksym name '-of-list-fix) hintsmap))
                              `((%cdr-induction x))))
            (local (%enable default ,(ACL2::mksym name '-of-list-fix)))

            (%autoprove ,(ACL2::mksym name '-of-app)
                        ,@(or (cdr (lookup (ACL2::mksym name '-of-app) hintsmap))
                              `((%cdr-induction x))))
            (local (%enable default ,(ACL2::mksym name '-of-app)))

            (%autoprove ,(ACL2::mksym name '-of-rev)
                        ,@(or (cdr (lookup (ACL2::mksym name '-of-rev) hintsmap))
                              `((%cdr-induction x))))
            (local (%enable default ,(ACL2::mksym name '-of-rev)))

            (%autoprove ,(ACL2::mksym elementp '-of-car-when- name)
                        ,@(cdr (lookup (ACL2::mksym elementp '-of-car-when- name) hintsmap)))
            (local (%enable default ,(ACL2::mksym elementp '-of-car-when- name)))

            (%autoprove ,(ACL2::mksym name '-of-cdr-when- name)
                        ,@(cdr (lookup (ACL2::mksym name '-of-cdr-when- name) hintsmap)))
            (local (%enable default ,(ACL2::mksym name '-of-cdr-when- name)))

            (%autoprove ,(ACL2::mksym elementp '-when-memberp-of- name)
                        ,@(or (cdr (lookup (ACL2::mksym elementp '-when-memberp-of- name) hintsmap))
                              `((%cdr-induction x))))
            (local (%enable default ,(ACL2::mksym elementp '-when-memberp-of- name)))

            (%autoprove ,(ACL2::mksym elementp '-when-memberp-of- name '-alt)
                        ,@(or (cdr (lookup (ACL2::mksym elementp '-when-memberp-of- name '-alt) hintsmap))
                              `((%use (%thm ,(ACL2::mksym elementp '-when-memberp-of- name))))))
            (local (%enable default ,(ACL2::mksym elementp '-when-memberp-of- name '-alt)))

            (%autoprove ,(ACL2::mksym name '-of-remove-all-when- name)
                        ,@(or (cdr (lookup (ACL2::mksym name '-of-remove-all-when- name) hintsmap))
                              `((%cdr-induction x))))
            (local (%enable default ,(ACL2::mksym name '-of-remove-all-when- name)))

            (%autoprove ,(ACL2::mksym name '-of-remove-duplicates)
                        ,@(or (cdr (lookup (ACL2::mksym name '-of-remove-duplicates) hintsmap))
                              `((%cdr-induction x))))
            (local (%enable default ,(ACL2::mksym name '-of-remove-duplicates)))

            (%autoprove ,(ACL2::mksym name '-of-difference-when- name)
                        ,@(or (cdr (lookup (ACL2::mksym name '-of-difference-when- name) hintsmap))
                              `((%cdr-induction x))))
            (local (%enable default ,(ACL2::mksym name '-of-difference-when- name)))

            (%autoprove ,(ACL2::mksym name '-of-subsetp-when- name)
                        ,@(or (cdr (lookup (ACL2::mksym name '-of-subsetp-when- name) hintsmap))
                              `((%cdr-induction x))))
            (local (%enable default ,(ACL2::mksym name '-of-subsetp-when- name)))

            (%autoprove ,(ACL2::mksym name '-of-subsetp-when- name '-alt)
                        ,@(or (cdr (lookup (ACL2::mksym name '-of-subsetp-when- name '-alt) hintsmap))
                              nil))
            (local (%enable default ,(ACL2::mksym name '-of-subsetp-when- name '-alt)))

            (%autoprove ,(ACL2::mksym name '-of-repeat)
                        ,@(or (cdr (lookup (ACL2::mksym name '-of-repeat) hintsmap))
                              `((%dec-induction y)
                                (%restrict default repeat (equal n 'y)))))
            (local (%enable default ,(ACL2::mksym name '-of-repeat)))

            ))))

(defmacro %deflist (name formals element &key negatedp hintsmap)
  (%deflist-fn name formals element negatedp hintsmap))




(defun %defprojection-fn (list element nil-preservingp hintsmap)
  (declare (xargs :mode :program))
  (let* ((list-fn   (car list))
         (elem-fn   (car element))
         ;; (elem-args (cdr element))
         (fast-fn   (if (ACL2::has-namespace list-fn)
                        (ACL2::mksym (ACL2::extract-namespace list-fn)
                               '.fast-
                               (ACL2::extract-nonnamespace list-fn)
                               '$)
                      (ACL2::mksym 'fast- list-fn '$))))
    `(defsection ,list-fn

       (local (%forcingp nil))

       (ACL2::make-event (if (tactic.find-rule ',list-fn
                                               (tactic.harness->world (ACL2::w ACL2::state)))
                             '(ACL2::value-triple :redundant)
                           '(%autoadmit ,list-fn)))

       (ACL2::make-event (if (or (tactic.find-rule ',fast-fn
                                                   (tactic.harness->world (ACL2::w ACL2::state)))
                                 (not (ACL2::get-untranslated-defun ',fast-fn (ACL2::w ACL2::state))))
                             '(ACL2::value-triple :redundant)
                           '(%autoadmit ,fast-fn)))

       (ACL2::make-event (if (tactic.find-rule ',(ACL2::mksym list-fn '-when-not-consp)
                                               (tactic.harness->world (ACL2::w ACL2::state)))
                             '(ACL2::value-triple :redundant)
                           '(%autoprove ,(ACL2::mksym list-fn '-when-not-consp)
                                        ,@(or (cdr (lookup (ACL2::mksym list-fn '-when-not-consp) hintsmap))
                                              `((%restrict default ,list-fn (equal x 'x)))))))
       (local (%enable default ,(ACL2::mksym list-fn '-when-not-consp)))

       (ACL2::make-event (if (tactic.find-rule ',(ACL2::mksym list-fn '-of-cons)
                                               (tactic.harness->world (ACL2::w ACL2::state)))
                             '(ACL2::value-triple :redundant)
                           '(%autoprove ,(ACL2::mksym list-fn '-of-cons)
                                        ,@(or (cdr (lookup (ACL2::mksym list-fn '-of-cons) hintsmap))
                                              `((%restrict default ,list-fn (equal x '(cons a x))))))))
       (local (%enable default ,(ACL2::mksym list-fn '-of-cons)))

       (%autoprove ,(ACL2::mksym 'true-listp-of- list-fn)
                   ,@(or (cdr (lookup (ACL2::mksym 'true-listp-of- list-fn) hintsmap))
                         `((%cdr-induction x))))
       (local (%enable default ,(ACL2::mksym 'true-listp-of- list-fn)))

       (%autoprove ,(ACL2::mksym 'len-of- list-fn)
                   ,@(or (cdr (lookup (ACL2::mksym 'len-of- list-fn) hintsmap))
                         `((%cdr-induction x))))
       (local (%enable default ,(ACL2::mksym 'len-of- list-fn)))

       (%autoprove ,(ACL2::mksym 'consp-of- list-fn)
                   ,@(or (cdr (lookup (ACL2::mksym 'consp-of- list-fn) hintsmap))
                         `((%cdr-induction x))))
       (local (%enable default ,(ACL2::mksym 'consp-of- list-fn)))

       (%autoprove ,(ACL2::mksym 'car-of- list-fn)
                   ,@(cdr (lookup (ACL2::mksym 'car-of- list-fn) hintsmap)))
       (local (%enable default ,(ACL2::mksym 'car-of- list-fn)))

       (%autoprove ,(ACL2::mksym 'cdr-of- list-fn)
                   ,@(cdr (lookup (ACL2::mksym 'cdr-of- list-fn) hintsmap)))
       (local (%enable default ,(ACL2::mksym 'cdr-of- list-fn)))

       (%autoprove ,(ACL2::mksym list-fn '-under-iff)
                   ,@(cdr (lookup (ACL2::mksym list-fn '-under-iff) hintsmap)))
       (local (%enable default ,(ACL2::mksym list-fn '-under-iff)))

       (%autoprove ,(ACL2::mksym list-fn '-of-list-fix)
                   ,@(or (cdr (lookup (ACL2::mksym list-fn '-of-list-fix) hintsmap))
                         `((%cdr-induction x))))
       (local (%enable default ,(ACL2::mksym list-fn '-of-list-fix)))

       (%autoprove ,(ACL2::mksym list-fn '-of-app)
                   ,@(or (cdr (lookup (ACL2::mksym list-fn '-of-app) hintsmap))
                         `((%cdr-induction x))))
       (local (%enable default ,(ACL2::mksym list-fn '-of-app)))

       (%autoprove ,(ACL2::mksym 'rev-of- list-fn)
                   ,@(or (cdr (lookup (ACL2::mksym 'rev-of- list-fn) hintsmap))
                         `((%cdr-induction x))))
       (local (%enable default ,(ACL2::mksym 'rev-of- list-fn)))

       (%autoprove ,(ACL2::mksym list-fn '-of-rev)
                   ,@(cdr (lookup (ACL2::mksym list-fn '-of-rev) hintsmap)))
       ;; DO NOT ENABLE THIS (it will loop with rev-of-list-fn)
       ;; (local (%enable default ,(ACL2::mksym list-fn '-of-rev)))

       (%autoprove ,(ACL2::mksym 'firstn-of- list-fn)
                   ,@(or (cdr (lookup (ACL2::mksym 'firstn-of- list-fn) hintsmap))
                         `((%autoinduct firstn y x)
                           (%restrict default firstn (equal n 'y)))))
       (local (%enable default ,(ACL2::mksym 'firstn-of- list-fn)))

       (%autoprove ,(ACL2::mksym 'restn-of- list-fn)
                   ,@(or (cdr (lookup (ACL2::mksym 'restn-of- list-fn) hintsmap))
                         `((%autoinduct restn y x)
                           (%restrict default restn (equal n 'y)))))
       (local (%enable default ,(ACL2::mksym 'restn-of- list-fn)))

       (%autoprove ,(ACL2::mksym 'memberp-of- elem-fn '-in- list-fn '-when-memberp)
                   ,@(or (cdr (lookup (ACL2::mksym 'memberp-of- elem-fn '-in- list-fn '-when-memberp) hintsmap))
                         `((%cdr-induction x))))
       (local (%enable default ,(ACL2::mksym 'memberp-of- elem-fn '-in- list-fn '-when-memberp)))

       (%autoprove ,(ACL2::mksym 'subsetp-of- list-fn 's-when-subsetp)
                   ,@(or (cdr (lookup (ACL2::mksym 'subsetp-of- list-fn 's-when-subsetp) hintsmap))
                         `((%cdr-induction x))))
       (local (%enable default ,(ACL2::mksym 'subsetp-of- list-fn 's-when-subsetp)))

      ,@(if nil-preservingp

            `((%autoprove ,(ACL2::mksym 'nth-of- list-fn)
                          ,@(or (cdr (lookup (ACL2::mksym 'nth-of- list-fn) hintsmap))
                                `((%autoinduct nth)
                                  (%restrict default nth (equal n 'n)))))
              (local (%enable default ,(ACL2::mksym 'nth-of- list-fn))))

          nil)

      (ACL2::make-event (if (not (lookup ',fast-fn (tactic.harness->atbl (ACL2::w ACL2::state))))
                            '(ACL2::value-triple :invisible)
                          '(%autoprove ,(ACL2::mksym fast-fn '-removal)
                                       ,@(or (cdr (lookup (ACL2::mksym fast-fn '-removal) hintsmap))
                                             `((%autoinduct ,fast-fn)
                                               ;;(%induct (rank x)
                                               ;;         ((not (consp x))
                                               ;;          nil)
                                               ;;         ((consp x)
                                               ;;          (((x   (cdr x))
                                               ;;            (acc (cons (,elem-fn ,@(ACL2::subst '(car x) 'x elem-args)) acc))))))
                                               (%restrict default ,fast-fn (equal x 'x)))))))

      )))



(defmacro %defprojection (&key list element nil-preservingp hintsmap)
  (declare (xargs :guard (and (ACL2::symbol-listp list)
                              (ACL2::symbol-listp element)
                              (booleanp nil-preservingp)
                              (consp list)
                              (consp element)
                              (uniquep (cdr list))
                              (let ((element-vars (remove-constants (cdr element))))
                                (and (uniquep element-vars)
                                     (memberp 'x element-vars)
                                     (not (memberp 'a element-vars))
                                     (not (memberp 'y element-vars))
                                     (not (memberp 'acc element-vars))
                                     (subsetp element-vars (cdr list))
                                     (subsetp (cdr list) element-vars))))))
  (%defprojection-fn list element nil-preservingp hintsmap))





