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
(ACL2::set-current-package "MILAWA" ACL2::*the-live-state*)

(ACL2::defun ACL2::to-flat-string (x)
  (let ((ACL2::*print-circle* nil)
        (ACL2::*print-escape* t)
        #+DRAFT-ANSI-CL-2 (ACL2::*print-lines* nil)
        #+DRAFT-ANSI-CL-2 (ACL2::*print-miser-width* nil)
        #+DRAFT-ANSI-CL-2 (ACL2::*print-pprint-dispatch* nil)
        #+DRAFT-ANSI-CL-2 (ACL2::*print-readably* t)
        #+DRAFT-ANSI-CL-2 (ACL2::*print-right-margin* nil)
        (ACL2::*readtable* ACL2::*acl2-readtable*)
        (ACL2::*print-case* :upcase)
        (ACL2::*print-pretty* nil)
        (ACL2::*print-level* nil)
        (ACL2::*print-length* nil))
    (ACL2::prin1-to-string x)))

(ACL2::defparameter MILAWA::*rw.crewrite-depth* 0)

(ACL2::defun %untrace-crewrite ()
  (ACL2::progn
   (CCL:unadvise tactic.crewrite-first-tac)
   (CCL:unadvise tactic.crewrite-all-tac)
   (CCL:unadvise rw.crewrite-entry)
   (CCL:unadvise rw.crewrite-note-fn)
   nil))

(ACL2::defun %trace-crewrite ()
  (ACL2::progn
   (CCL:advise tactic.crewrite-first-tac
               (ACL2::setf *rw.crewrite-depth* 0)
               :when :before)
   (CCL:advise tactic.crewrite-all-tac
               (ACL2::setf *rw.crewrite-depth* 0)
               :when :before)
   (CCL:advise rw.crewrite-entry
               (let* ((arglist  CCL::arglist)
                      (flag     (nth 0 arglist))
                      (assms    (nth 1 arglist))
                      (x        (nth 2 arglist))
                      (rule[s]  (nth 3 arglist))
                      (sigma[s] (nth 4 arglist))
                      (hypcache (nth 5 arglist))
                      (iffp     (nth 6 arglist))
                      (blimit   (nth 7 arglist))
                      (rlimit   (nth 8 arglist))
                      (anstack  (nth 9 arglist))
                      (control  (nth 10 arglist)))
                 (declare (ACL2::ignorable flag assms x rule[s] sigma[s] hypcache iffp blimit rlimit anstack control))
                 (cond ((equal flag 'term)
                        (ACL2::prog2$
                         (ACL2::setf *rw.crewrite-depth* (+ *rw.crewrite-depth* 1))
                         (ACL2::fmt1! "~s0~x1> ~x2 ~s3~%~
                                   ~s0~x1> Assms ~s4~%"
                                      (list (cons #\0 (ACL2::coerce (repeat #\Space *rw.crewrite-depth*) 'ACL2::string))
                                            (cons #\1 *rw.crewrite-depth*)
                                            (cons #\2 (if iffp 'RW_IFF 'RW_EQL))
                                            (cons #\3 (ACL2::to-flat-string x))
                                            (cons #\4 (ACL2::to-flat-string (%print-negate-hyps
                                                                             (fast-app
                                                                              (rw.hypbox->left (rw.assms->hypbox assms))
                                                                              (rw.hypbox->right (rw.assms->hypbox assms)))))))
                                      0
                                      ACL2::*standard-co*
                                      ACL2::*the-live-state*
                                      nil)))
                       ((equal flag 'rule)
                        (ACL2::fmt1! "~s0~x1> ~x2: try matching ~s3~%"
                                     (list (cons #\0 (ACL2::coerce (repeat #\Space *rw.crewrite-depth*) 'ACL2::string))
                                           (cons #\1 *rw.crewrite-depth*)
                                           (cons #\2 (rw.rule->name rule[s]))
                                           (cons #\3 (ACL2::to-flat-string (rw.rule->lhs rule[s]))))
                                     0
                                     ACL2::*standard-co*
                                     ACL2::*the-live-state*
                                     nil))
                       ((equal flag 'match)
                        (ACL2::fmt1! "~s0~x1> ~x2: try sigma ~s3~%"
                                     (list (cons #\0 (ACL2::coerce (repeat #\Space *rw.crewrite-depth*) 'ACL2::string))
                                           (cons #\1 *rw.crewrite-depth*)
                                           (cons #\2 (rw.rule->name rule[s]))
                                           (cons #\3 (ACL2::to-flat-string sigma[s])))
                                     0
                                     ACL2::*standard-co*
                                     ACL2::*the-live-state*
                                     nil))
                       ((equal flag 'hyp)
                        (let ((goal (logic.substitute (rw.hyp->term x) sigma[s])))
                          (ACL2::fmt1! "~s0~x1> ~x2: hyp instance: ~s3~%"
                                       (list (cons #\0 (ACL2::coerce (repeat #\Space *rw.crewrite-depth*) 'ACL2::string))
                                             (cons #\1 *rw.crewrite-depth*)
                                             (cons #\2 (rw.rule->name rule[s]))
                                             (cons #\3 (ACL2::to-flat-string goal)))
                                       0
                                       ACL2::*standard-co*
                                       ACL2::*the-live-state*
                                       nil)))
                       (t nil)))
               :when :before)
   (CCL:advise rw.crewrite-note-fn
               (let* ((arglist  CCL::arglist)
                      (flag     (nth 0 arglist))
                      (assms    (nth 1 arglist))
                      (x        (nth 2 arglist))
                      (rule[s]  (nth 3 arglist))
                      (sigma[s] (nth 4 arglist))
                      (hypcache (nth 5 arglist))
                      (iffp     (nth 6 arglist))
                      (blimit   (nth 7 arglist))
                      (rlimit   (nth 8 arglist))
                      (anstack  (nth 9 arglist))
                      (control  (nth 10 arglist))
                      (note     (nth 11 arglist)))
                 (declare (ACL2::ignorable flag assms x rule[s] sigma[s] hypcache iffp blimit rlimit anstack control note))
                 (ACL2::prog2$
                  (ACL2::fmt1! "~s0<~x1 NOTE: ~s2~%"
                               (list (cons #\0 (ACL2::coerce (repeat #\Space *rw.crewrite-depth*) 'ACL2::string))
                                     (cons #\1 *rw.crewrite-depth*)
                                     (cons #\2 (ACL2::to-flat-string note)))
                               0
                               ACL2::*standard-co*
                               ACL2::*the-live-state*
                               nil)
                  (if (equal (car note) 'rewrote-to)
                      (ACL2::setf *rw.crewrite-depth* (- *rw.crewrite-depth* 1))
                    nil)))
               :when :before)
   nil))