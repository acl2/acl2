; Centaur Miscellaneous Books
; Copyright (C) 2012 Centaur Technology
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
; fast AIG variable collection cheat using destructive consing -- raw Lisp
; Original author: Sol Swords <sswords@centtech.com>

;; With destructive memoization on X using restore-array as the restore array,
;; accumulates the not-previously-seen AIG vars of X into acc.
(defun accumulate-aig-vars-fast (x restore-array vartable acc)
  (b* (((when (aig-atom-p x)) (if (or (booleanp x)
                                (gethash x vartable))
                            (mv restore-array acc)
                          (progn 
                            (setf (gethash x vartable) t)
                            (mv restore-array (cons x acc)))))
       ((when (eq (cdr x) nil))
        (accumulate-aig-vars-fast (car x) restore-array vartable acc))
       ((when (cons-was-visited x restore-array))
        (mv restore-array acc))
       ((cons car cdr) x)
       (restore-array (mark-visited-cons x t restore-array))
       ((mv restore-array acc)
        (accumulate-aig-vars-fast car restore-array vartable acc)))
    (accumulate-aig-vars-fast cdr restore-array vartable acc)))

(defun aig-vars-unordered (x)
  (with-fast-cons-memo
    :fnname aig-vars-unordered
    :return-vals (acc)
    :restore-array restore-arr
    :initial-size 16
    :body (b* (((mv ?restore-arr acc)
                (accumulate-aig-vars-fast
                 (hons-copy x)
                 restore-arr
                 (make-hash-table :test 'eql)
                 nil)))
            acc)))

(defun aig-vars-unordered-list (x)
  (with-fast-cons-memo
    :fnname aig-vars-unordered
    :return-vals (acc)
    :restore-array restore-arr
    :initial-size 16
    :body (b* ((acc nil)
               (vartable (make-hash-table :test 'eql))
               ((mv ?restore-arr acc)
                (if (true-listp x)
                    (progn (loop for elt in x do
                                 (multiple-value-setq (restore-arr acc)
                                   (accumulate-aig-vars-fast elt restore-arr
                                                             vartable acc)))
                           (mv restore-arr acc))
                  (accumulate-aig-vars-fast x restore-arr vartable acc))))
            acc)))



(defun aig-vars1 (x nodetable acc)
  (if (aig-atom-p x)
      (if (or (booleanp x) (gethash x nodetable))
          acc
        (progn (setf (gethash x nodetable) t)
               (cons x acc)))
    (if (cdr x)
        (if (gethash x nodetable)
            acc
          (progn
            (setf (gethash x nodetable) t)
            (let ((acc (aig-vars1 (car x) nodetable acc)))
              (aig-vars1 (cdr x) nodetable acc))))
      (aig-vars1 (car x) nodetable acc))))
          
         
(unless (fboundp 'aig-vars-memo)
  (setf (symbol-function 'aig-vars-memo)
        (symbol-function 'aig-vars)))

(defun aig-vars-1pass (x)
  (alphorder-sort (aig-vars-unordered x)))
  ;;(let ((nodetable (make-hash-table :test 'eql))
  ;;      (x (hons-copy x)))
  ;;  (alphorder-sort
  ;;   (aig-vars1 x nodetable nil))))

(defun aigtab-collect-vars1-raw (queue aigtab-ht restore-arr vartable seen)
  (b* (((when (atom queue)) (mv seen restore-arr))
       (seen (cons (car queue) seen))
       ((mv val boundp) (gethash (car queue) aigtab-ht))
       ((unless boundp)
        (aigtab-collect-vars1-raw
         (cdr queue) aigtab-ht restore-arr vartable seen))
       ((mv restore-arr queue)
        (accumulate-aig-vars-fast
         val restore-arr vartable (cdr queue))))
    (aigtab-collect-vars1-raw
     queue aigtab-ht restore-arr vartable seen)))


;;(defun aigtab-collect-vars1-raw (queue aigtab nodetable seen)
;;  (b* (((when (Atom queue)) seen)
;;       (seen (cons (car queue) seen))
;;       (aig (cdr (hons-get (car queue) aigtab)))
;;       (queue (aig-vars1 (hons-copy aig) nodetable (cdr queue))))
;;    (aigtab-collect-vars1-raw queue aigtab nodetable seen)))

(defun aigtab-collect-vars (queue aigtab)
  (with-fast-cons-memo
    :fnname aigtab-collect-vars
    :return-vals (seen)
    :restore-array restore-arr
    :initial-size (* 5 (len queue))
    :body (b* (((with-fast aigtab))
               (ht (let* ((faltable (hl-hspace-faltable *default-hs*))
                          (slot     (hl-faltable-general-lookup aigtab faltable)))
                     (hl-falslot-val slot)))
               (vartable (make-hash-table :test 'eql :size (* 2 (len queue))))
               (- (loop for v in queue do (setf (gethash v vartable) t)))
               ((mv seen ?restore-arr)
                (aigtab-collect-vars1-raw
                 queue ht restore-arr
                 vartable
                 nil)))
            seen))
  ;;(b* ((nodetable (make-hash-table :test 'eql))
  ;;     (- (loop for var in queue do
  ;;              (setf (gethash var nodetable) t))))
  ;;  (aigtab-collect-vars1-raw queue aigtab nodetable nil))
  )


(defun merge-into-nodetable/acc (lst nodetable acc)
  (loop for x in lst do
        (unless (gethash x nodetable)
          (setf (gethash x nodetable) t)
          (push x acc)))
  acc)

(declaim (ftype (function (t t t t) (values t))
                aig-vars-fast1))

(defun aig-vars-fast (x)
  (progn
    (aig-vars '(t . t)) ;; this ensures that the AIG-VARS memo table is
    ;; initialized.
    (b* ((nodetable (make-hash-table :test 'eql))
         (memtable (symbol-value (third (gethash 'aig-vars
                                                 *memoize-info-ht*))))
         (x (hons-copy x))
         (ans (alphorder-sort
               (aig-vars-fast1 x nodetable memtable nil))))
      (setf (gethash x memtable) ans))))

(unless (memoizedp-raw 'aig-vars-fast)
  (mf-note-arity 'aig-vars-fast 1 1)
  (profile 'aig-vars-fast))

(defg *aig-vars-fast1-hits* 0)
(defg *aig-vars-fast1-calls* 0)


(defun aig-vars-fast1 (x nodetable memtable acc)
  (if (aig-atom-p x)
      (if (or (booleanp x)
              (gethash x nodetable))
          acc
        (progn
          (setf (gethash x nodetable) t)
          (cons x acc)))
    (if (cdr x)
        (if (gethash x nodetable)
            acc
          (progn (setf (gethash x nodetable) t)
                 (incf *aig-vars-fast1-calls*)
                 (multiple-value-bind (mem memp)
                     (gethash x memtable)
                   (if memp
                       (progn
                         (incf *aig-vars-fast1-hits*)
                         (merge-into-nodetable/acc mem nodetable acc))
                     (aig-vars-fast1 (cdr x) nodetable memtable
                                     (aig-vars-fast1 (car x) nodetable memtable acc))))))
      (aig-vars-fast1 (car x) nodetable memtable acc))))


