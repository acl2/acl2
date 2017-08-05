; ACL2 interface to the ZZ system
; Copyright (C) 2011-2017 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "zz")
(include-book "zzv-interface")
(include-book "centaur/misc/sneaky-load" :dir :system)

(defun zzv-sat-raw (aig timeout)
  (declare (xargs :guard t))
  (zz-sat aig :timeout (and timeout (nfix timeout))))

(defthm zzv-sat-raw-consp
  (consp (zzv-sat-raw aig timeout))
  :rule-classes :type-prescription)

(defthm zzv-sat-raw-sat
  (implies (equal (car (zzv-sat-raw aig timeout)) 'sat)
           (aig-eval aig (cdr (zzv-sat-raw aig timeout)))))

(defthm zzv-sat-raw-unsat
  (implies (equal (car (zzv-sat-raw aig timeout)) 'unsat)
           (not (aig-eval aig env))))

(in-theory (disable zzv-sat-raw))

(defmacro zzv-sat-raw-mode ()
  '(defattach (zzv-sat-fn zzv-sat-raw)
     :hints (("goal" :in-theory '(zzv-sat-raw-consp
                                  zzv-sat-raw-sat
                                  zzv-sat-raw-unsat)))))

(encapsulate nil
  ;; just make sure it works
  (local (zzv-sat-raw-mode)))



(defun zzv-sat-record (aig timeout)
  (declare (xargs :guard t))
  (b* ((res (zz-sat aig :timeout (and timeout (nfix timeout))
                    :mk-proof t))
       (pair (cons (hons aig timeout) res))
       (- (sneaky-push 'zzv-sat-results pair)))
    res))

(defthm zzv-sat-record-consp
  (consp (zzv-sat-record aig timeout))
  :rule-classes :type-prescription)

(defthm zzv-sat-record-sat
  (implies (equal (car (zzv-sat-record aig timeout)) 'sat)
           (aig-eval aig (cdr (zzv-sat-record aig timeout)))))

(defthm zzv-sat-record-unsat
  (implies (equal (car (zzv-sat-record aig timeout)) 'unsat)
           (not (aig-eval aig env))))

(in-theory (disable zzv-sat-record))

(defmacro zzv-sat-record-mode ()
  '(defattach (zzv-sat-fn zzv-sat-record)
     :hints (("goal" :in-theory '(zzv-sat-record-consp
                                  zzv-sat-record-sat
                                  zzv-sat-record-unsat)))))

(encapsulate nil
  ;; just make sure it works
  (local (zzv-sat-record-mode)))







(defun zzv-batch-sat-raw (aigs timeout)
  (declare (xargs :guard t))
  (zz-batch-sat aigs :timeout (and timeout (nfix timeout))))

(defthm zzv-batch-sat-raw-len
  (equal (len (zzv-batch-sat-raw aigs timeout))
         (len aigs)))

(defthm zzv-batch-sat-raw-entries-consp
  (implies (member-equal entry (zzv-batch-sat-raw aigs timeout))
           (consp entry)))

(defthm zzv-batch-sat-raw-entry-sat
  (implies (equal (car (nth n (zzv-batch-sat-raw aigs timeout))) 'sat)
           (aig-eval (nth n aigs)
                     (cdr (nth n (zzv-batch-sat-raw
                                  aigs timeout))))))

(defthm zzv-batch-sat-raw-entry-unsat
  (implies (equal (car (nth n (zzv-batch-sat-raw aigs timeout))) 'unsat)
           (not (aig-eval (nth n aigs) env))))

(defmacro zzv-batch-sat-raw-mode ()
  '(defattach (zzv-batch-sat-fn zzv-batch-sat-raw)
     :hints (("goal" :in-theory '(zzv-batch-sat-raw-len
                                  zzv-batch-sat-raw-entries-consp
                                  zzv-batch-sat-raw-entry-sat
                                  zzv-batch-sat-raw-entry-unsat)))))

(encapsulate nil
  (local (zzv-batch-sat-raw-mode)))




(defun zzv-batch-sat-record (aigs timeout)
  (declare (xargs :guard t))
  (b* ((res (zz-batch-sat aigs :timeout (and timeout (nfix timeout))
                    :mk-proof t))
       (pair (cons (hons aigs timeout) res))
       (- (sneaky-push 'zzv-batch-sat-results pair)))
    res))

(defthm zzv-batch-sat-record-len
  (equal (len (zzv-batch-sat-record aigs timeout))
         (len aigs)))

(defthm zzv-batch-sat-record-entries-consp
  (implies (member-equal entry (zzv-batch-sat-record aigs timeout))
           (consp entry)))

(defthm zzv-batch-sat-record-entry-sat
  (implies (equal (car (nth n (zzv-batch-sat-record aigs timeout))) 'sat)
           (aig-eval (nth n aigs)
                     (cdr (nth n (zzv-batch-sat-record
                                  aigs timeout))))))

(defthm zzv-batch-sat-record-entry-unsat
  (implies (equal (car (nth n (zzv-batch-sat-record aigs timeout))) 'unsat)
           (not (aig-eval (nth n aigs) env))))

(defmacro zzv-batch-sat-record-mode ()
  '(defattach (zzv-batch-sat-fn zzv-batch-sat-record)
     :hints (("goal" :in-theory '(zzv-batch-sat-record-len
                                  zzv-batch-sat-record-entries-consp
                                  zzv-batch-sat-record-entry-sat
                                  zzv-batch-sat-record-entry-unsat)))))

(encapsulate nil
  (local (zzv-batch-sat-record-mode)))




(defun zzv-modelcheck-raw (stepfns prop initsts timeout max-depth engine)
  (declare (xargs :guard t))
  (zz-modelcheck stepfns prop initsts timeout max-depth nil nil engine))

(defthm consp-zzv-modelcheck-raw
  (consp (zzv-modelcheck-raw stepfns prop initsts timeout max-depth engine))
  :rule-classes :type-prescription)


(defthm consp-zzv-modelcheck-raw-trace-when-refuted
  (let ((res (zzv-modelcheck-raw stepfns prop initsts timeout max-depth engine)))
    (implies (equal (car res) 'refuted)
             (and (consp (cdr res))
                  (consp (cddr res))))))

(defthm zzv-modelcheck-raw-when-refuted
  (let ((res (zzv-modelcheck-raw stepfns prop initsts timeout max-depth engine)))
    (implies (equal (car res) 'refuted)
             (and (equal (check-property stepfns prop (cadr res) (cddr res))
                         nil)
                  (alists-agree (alist-keys initsts) initsts (cadr res))))))

(defthm zzv-modelcheck-raw-when-proved
  (implies
   (and (equal (car (zzv-modelcheck-raw
                     stepfns prop initsts timeout max-depth engine))
               'proved)
        (alists-agree (alist-keys initsts) initsts ctrex-initst))
   (check-property stepfns prop ctrex-initst ctrex-frames))
  :hints(("Goal" :in-theory (disable hons-subset))))

(in-theory (disable zzv-modelcheck-raw))

(defmacro zzv-modelcheck-raw-mode ()
  '(defattach (zzv-modelcheck zzv-modelcheck-raw)
     :hints (("goal" :in-theory '(consp-zzv-modelcheck-raw
                                  consp-zzv-modelcheck-raw-trace-when-refuted
                                  zzv-modelcheck-raw-when-refuted
                                  zzv-modelcheck-raw-when-proved)))))

(encapsulate nil
  (local (zzv-modelcheck-raw-mode)))




(defun zzv-get-proof (aig name)
  (declare (Xargs :guard t))
  (b* ((res (zz-sat aig :mk-proof t))
       (- (or (eq (car res) 'unsat)
              (er hard? 'zzv-get-proof
                  "ZZV-GET-PROOF: ~s0 property did not prove. Result: ~x1~%"
                  name res))))
    (cdr res)))
  

(defun zzv-modelcheck-record (stepfns prop initsts timeout max-depth engine)
  (declare (xargs :guard t))
  (b* ((res (zz-modelcheck stepfns prop initsts timeout max-depth t nil
                           engine))
       (key (hons-list* stepfns prop initsts timeout max-depth engine))
       ((when (not (eq (car res) 'proved)))
        (sneaky-push 'zzv-modelcheck-results
                     (cons key res))
        res)
       (invar (cdr res))
       (inductivity-proof
        (with-fast-alist stepfns
          (zzv-get-proof (aig-and invar (aig-not (aig-restrict invar stepfns)))
                         'inductivity)))
       (sufficiency-proof
        (zzv-get-proof (aig-and invar (aig-not prop))
                       'sufficiency))
       (initialization-proof
        (with-fast-alist initsts
          (zzv-get-proof (aig-not (aig-partial-eval invar initsts))
                         'initialization)))
       (res (list* 'proved
                   invar
                   inductivity-proof
                   sufficiency-proof
                   initialization-proof)))
    (sneaky-push 'zzv-modelcheck-results
                 (cons key res))
    res))

(defthm consp-zzv-modelcheck-record
  (consp (zzv-modelcheck-record stepfns prop initsts timeout max-depth engine))
  :rule-classes :type-prescription)


(defthm consp-zzv-modelcheck-record-trace-when-refuted
  (let ((res (zzv-modelcheck-record stepfns prop initsts timeout max-depth engine)))
    (implies (equal (car res) 'refuted)
             (and (consp (cdr res))
                  (consp (cddr res))))))

(defthm zzv-modelcheck-record-when-refuted
  (let ((res (zzv-modelcheck-record stepfns prop initsts timeout max-depth engine)))
    (implies (equal (car res) 'refuted)
             (and (equal (check-property stepfns prop (cadr res) (cddr res))
                         nil)
                  (alists-agree (alist-keys initsts) initsts (cadr res))))))

(defthm zzv-modelcheck-record-when-proved
  (implies
   (and (equal (car (zzv-modelcheck-record
                     stepfns prop initsts timeout max-depth engine))
               'proved)
        (alists-agree (alist-keys initsts) initsts ctrex-initst))
   (check-property stepfns prop ctrex-initst ctrex-frames))
  :hints(("Goal" :in-theory (disable hons-subset))))

(in-theory (disable zzv-modelcheck-record))

(defmacro zzv-modelcheck-record-mode ()
  '(defattach (zzv-modelcheck zzv-modelcheck-record)
     :hints (("goal" :in-theory '(consp-zzv-modelcheck-record
                                  consp-zzv-modelcheck-record-trace-when-refuted
                                  zzv-modelcheck-record-when-refuted
                                  zzv-modelcheck-record-when-proved)))))

(encapsulate nil
  (local (zzv-modelcheck-record-mode)))



(defmacro zzv-raw-mode ()
  '(progn (zzv-sat-raw-mode)
          (zzv-batch-sat-raw-mode)
          (zzv-modelcheck-raw-mode)))

(defmacro zzv-record-mode ()
  '(progn (zzv-sat-record-mode)
          (zzv-batch-sat-record-mode)
          (zzv-modelcheck-record-mode)))
