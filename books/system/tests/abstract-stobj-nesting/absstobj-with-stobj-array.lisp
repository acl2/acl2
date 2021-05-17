; Some Tests of Abstract Stobjs with Stobj Fields
; Copyright (C) 2021 Centaur Technology
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
; Additional contributions: Matt Kaufmann <matthew.j.kaufmann@gmail.com>

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Example 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj sub$c fld0$c)
(defstobj top$c (subs$c :type (array sub$c (0)) :resizable t))

(defun top$ap (x)
  (declare (xargs :guard t))
  (true-listp x))

(defun resize-subs$a (n x)
  (declare (xargs :guard (and (natp n)
                              (top$ap x))))
  (resize-list x n nil))

(defun subs$a-length (x)
  (Declare (xargs :guard t))
  (len x))

; At one point it was necessary for the second input below to be the stobj
; sub$c, as shown in the commented-out definition just below.  That was
; necessary so that the input signature of update-subs$ai would match that of
; update-subs$ci, these being the :logic and :exec functions for the
; defabsstobj export, update-subsi (see the defabsstobj event below).  That is
; however no longer necessary.
#||
(defun update-subs$ai (n sub$c x)
  (declare (xargs :guard (and (natp n)
                              (top$ap x)
                              (< n (subs$a-length x)))
                  :stobjs sub$c))
  (update-nth n (non-exec (fld0$c sub$c)) x))
||#

(defun update-subs$ai (n sub x)
  (declare (xargs :guard (and (natp n)
                              (top$ap x)
                              (sub$cp sub)
                              (< n (subs$a-length x)))))
  (update-nth n (non-exec (fld0$c sub)) x))

(defun subs$ai (n x)
  (Declare (xargs :guard (and (top$ap x)
                              (natp n)
                              (< n (subs$a-length x)))))
  (non-exec (update-fld0$c (nth n x)
                           (create-sub$c))))

(defun create-top$a ()
  (Declare (xargs :guard t))
  nil)

(defun-sk top-fields-corr (x y)
  (forall n
          (implies (< (nfix n) (len x))
                   (equal (list (nth n y)) (nth n x))))
  :rewrite :direct)
(in-theory (disable top-fields-corr))

(defun top-corr (x y)
  (non-exec
   (and (equal (len (car x)) (len y))
        (top-fields-corr (car x) y))))


(local (defthm len-of-resize-list
         (equal (len (resize-list lst n x))
                (nfix n))))

(local (defthm consp-of-resize-list
         (equal (consp (resize-list lst n x))
                (posp n))))

(local (defthm car-of-resize-list
         (equal (car (Resize-list lst n default))
                (cond ((zp n) nil)
                      ((atom lst) default)
                      (t (car lst))))))

(local (defthm caar-when-top-fields-corr
         (implies (and (top-fields-corr (car top$c) top)
                       (consp (car top$c)))
                  (equal (car (car top$c)) (list (car top))))
         :hints (("goal" :use ((:instance top-fields-corr-necc
                                (x (car top$c)) (y top)
                                (n 0)))))))

(local (defthm resize-list-when-not-consp
         (implies (and (syntaxp (not (equal x ''nil)))
                       (not (consp x)))
                  (equal (resize-list x n default)
                         (resize-list nil n default)))))

(local
 (encapsulate nil
   (local (defun nth-of-resize-list-ind (k n x)
            (if (zp k)
                (list n x)
              (nth-of-resize-list-ind (1- k) (1- n) (cdr x)))))
   (defthm nth-of-resize-list
     (equal (nth k (resize-list lst n default))
            (cond ((<= (nfix n) (nfix k)) nil)
                  ((< (nfix k) (len lst)) (nth k lst))
                  (t default)))
     :hints (("goal" :induct (nth-of-resize-list-ind k n lst)
              :expand ((resize-list lst n default)))))))

(local (defthm equal-of-len
         (implies (syntaxp (quotep n))
                  (equal (equal (len x) n)
                         (cond ((equal n 0) (atom x))
                               ((zp n) nil)
                               (t (and (consp x)
                                       (equal (len (cdr x)) (1- n)))))))))

(encapsulate nil

  (set-default-hints
   '((and stable-under-simplificationp
          (let ((lit (car (last clause))))
            (and (consp lit)
                 (eq (car lit) 'top-fields-corr)
                 `(:expand ,lit))))))

  (DEFTHM CREATE-TOP{CORRESPONDENCE}
    (TOP-CORR (CREATE-TOP$C) (CREATE-TOP$A))
    :RULE-CLASSES NIL)

  (DEFTHM CREATE-TOP{PRESERVED}
    (TOP$AP (CREATE-TOP$A))
    :RULE-CLASSES NIL)

  (DEFTHM SUBS-LENGTH{CORRESPONDENCE}
    (IMPLIES (TOP-CORR TOP$C TOP)
             (EQUAL (SUBS$C-LENGTH TOP$C)
                    (SUBS$A-LENGTH TOP)))
    :RULE-CLASSES NIL)

  (DEFTHM RESIZE-SUBS{CORRESPONDENCE}
    (IMPLIES (AND (TOP-CORR TOP$C TOP)
                  (NATP I)
                  (TOP$AP TOP))
             (TOP-CORR (RESIZE-SUBS$C I TOP$C)
                       (RESIZE-SUBS$A I TOP)))
    :RULE-CLASSES NIL)

  (DEFTHM RESIZE-SUBS{PRESERVED}
    (IMPLIES (AND (NATP I) (TOP$AP TOP))
             (TOP$AP (RESIZE-SUBS$A I TOP)))
    :RULE-CLASSES NIL)

  (DEFTHM SUBSI{CORRESPONDENCE}
    (IMPLIES (AND (TOP-CORR TOP$C TOP)
                  (TOP$AP TOP)
                  (NATP I)
                  (< I (SUBS$A-LENGTH TOP)))
             (EQUAL (SUBS$CI I TOP$C)
                    (SUBS$AI I TOP)))
    :RULE-CLASSES NIL)

  (DEFTHM SUBSI{GUARD-THM}
    (IMPLIES (AND (TOP-CORR TOP$C TOP)
                  (TOP$AP TOP)
                  (NATP I)
                  (< I (SUBS$A-LENGTH TOP)))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SUBS$C-LENGTH TOP$C))))
    :RULE-CLASSES NIL)

  (DEFTHM UPDATE-SUBSI{CORRESPONDENCE}
    (IMPLIES (AND (TOP-CORR TOP$C TOP)
                  (NATP I)
                  (TOP$AP TOP)
                  (SUB$CP SUB$C)
                  (< I (SUBS$A-LENGTH TOP)))
             (TOP-CORR (UPDATE-SUBS$CI I SUB$C TOP$C)
                       (UPDATE-SUBS$AI I SUB$C TOP)))
    :RULE-CLASSES NIL)

  (DEFTHM UPDATE-SUBSI{GUARD-THM}
    (IMPLIES (AND (TOP-CORR TOP$C TOP)
                  (NATP I)
                  (TOP$AP TOP)
                  (SUB$CP SUB$C)
                  (< I (SUBS$A-LENGTH TOP)))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SUBS$C-LENGTH TOP$C))))
    :RULE-CLASSES NIL)

  (DEFTHM UPDATE-SUBSI{PRESERVED}
    (IMPLIES (AND (NATP I)
                  (TOP$AP TOP)
                  (SUB$CP SUB$C)
                  (< I (SUBS$A-LENGTH TOP)))
             (TOP$AP (UPDATE-SUBS$AI I SUB$C TOP)))
    :RULE-CLASSES NIL)

  (DEFTHM SUBS2I{CORRESPONDENCE}
    (IMPLIES (AND (TOP-CORR TOP$C TOP)
                  (TOP$AP TOP)
                  (NATP I)
                  (< I (SUBS$A-LENGTH TOP)))
             (EQUAL (SUBS$CI I TOP$C)
                    (SUBS$AI I TOP)))
    :RULE-CLASSES NIL)

  (DEFTHM SUBS2I{GUARD-THM}
    (IMPLIES (AND (TOP-CORR TOP$C TOP)
                  (TOP$AP TOP)
                  (NATP I)
                  (< I (SUBS$A-LENGTH TOP)))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SUBS$C-LENGTH TOP$C))))
    :RULE-CLASSES NIL)

  (DEFTHM UPDATE-SUBS2I{CORRESPONDENCE}
    (IMPLIES (AND (TOP-CORR TOP$C TOP)
                  (NATP I)
                  (TOP$AP TOP)
                  (SUB$CP SUB$C)
                  (< I (SUBS$A-LENGTH TOP)))
             (TOP-CORR (UPDATE-SUBS$CI I SUB$C TOP$C)
                       (UPDATE-SUBS$AI I SUB$C TOP)))
    :RULE-CLASSES NIL)

  (DEFTHM UPDATE-SUBS2I{GUARD-THM}
    (IMPLIES (AND (TOP-CORR TOP$C TOP)
                  (NATP I)
                  (TOP$AP TOP)
                  (SUB$CP SUB$C)
                  (< I (SUBS$A-LENGTH TOP)))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SUBS$C-LENGTH TOP$C))))
    :RULE-CLASSES NIL)

  (DEFTHM UPDATE-SUBS2I{PRESERVED}
    (IMPLIES (AND (NATP I)
                  (TOP$AP TOP)
                  (SUB$CP SUB$C)
                  (< I (SUBS$A-LENGTH TOP)))
             (TOP$AP (UPDATE-SUBS$AI I SUB$C TOP)))
    :RULE-CLASSES NIL)

  (defabsstobj top
    :concrete top$c
    :corr-fn top-corr
    :recognizer (topp :logic top$ap :exec top$cp)
    :creator (create-top :logic create-top$a :exec create-top$c)
    :exports ((subs-length :logic subs$a-length :exec subs$c-length)
              (resize-subs :logic resize-subs$a :exec resize-subs$c)
              (subsi :logic subs$ai :exec subs$ci :updater update-subsi)
              (update-subsi :logic update-subs$ai :exec update-subs$ci)

              (subs2i :logic subs$ai :exec subs$ci :updater update-subs2i)
              (update-subs2i :logic update-subs$ai :exec update-subs$ci))))


(defstobj sub1$c fld1$c :congruent-to sub$c)
(defstobj sub2$c fld2$c :congruent-to sub$c)

; The following fails even without a guard verification attempt, because in the
; stobj-let form: ultimately subsi and subs2i both access the same field,
; subs$c, of the same foundational stobj, top$c, of top.  It seems best to
; catch such errors before guard verification is even attempted, since the
; stobj-let call would always fail a duplicate-indices check anyhow.
(must-fail
(defun foo-fails-1 (n top)
  (declare (xargs :stobjs top
                  :verify-guards nil
                  :guard (and (natp n)
                              (< n (subs-length top)))))
  (stobj-let ((sub1$c (subsi n top))
              (sub2$c (subs2i n top)))
             (sub1$c sub2$c)
             (let* ((val1 (fld0$c sub1$c))
                    (val2 (fld0$c sub2$c))
                    (sub1$c (update-fld0$c (+ 1 (ifix val2)) sub1$c))
                    (sub2$c (update-fld0$c (+ 2 (ifix val1)) sub2$c)))
               (mv sub1$c sub2$c))
             top))
)

; The following fails because the a guard condition, (not (equal n m)), has
; been omitted.  That part of the guard is necessary to avoid an aliasing
; problem.
(must-fail
(defun foo-fails-2 (n m top)
  (declare (xargs :stobjs top
                  :guard (and (natp n) (natp m)
                              (< n (subs-length top))
                              (< m (subs-length top))
                              ;; (not (equal n m))
                              )))
  (stobj-let ((sub1$c (subsi n top))
              (sub2$c (subs2i m top)))
             (sub1$c sub2$c)
             (let* ((val1 (fld0$c sub1$c))
                    (val2 (fld0$c sub2$c))
                    (sub1$c (update-fld0$c (+ 1 (ifix val2)) sub1$c))
                    (sub2$c (update-fld0$c (+ 2 (ifix val1)) sub2$c)))
               (mv sub1$c sub2$c))
             top))
)

(defun foo (n m top)
  (declare (xargs :stobjs top
                  :guard (and (natp n) (natp m)
                              (< n (subs-length top))
                              (< m (subs-length top))
                              (not (equal n m)) ; necessary!
                              )))
  (stobj-let ((sub1$c (subsi n top))
              (sub2$c (subs2i m top))) ; same concrete accessor ok since n != m
             (sub1$c sub2$c)
             (let* ((val1 (fld0$c sub1$c))
                    (val2 (fld0$c sub2$c))
                    (sub1$c (update-fld0$c (+ 1 (ifix val2)) sub1$c))
                    (sub2$c (update-fld0$c (+ 2 (ifix val1)) sub2$c)))
               (mv sub1$c sub2$c))
             top))

(defun vals (n top)
  (declare (xargs :stobjs top
                  :guard (and (natp n)
                              (<= n (subs-length top)))
                  :measure (nfix (- (subs-length top) (nfix n)))))
  (if (zp (- (subs-length top) (nfix n)))
      nil
    (cons (stobj-let ((sub$c (subsi n top)))
                     (val)
                     (fld0$c sub$c)
                     val)
          (vals (1+ (nfix n)) top))))

(local (defthm nthcdr-of-nil
         (equal (nthcdr n nil) nil)))

(local (defthmd equal-of-cons
         (equal (equal (cons x y) z)
                (and (consp z)
                     (equal x (car z))
                     (equal y (cdr z))))))

(local (defthm consp-of-nthcdr
         (iff (consp (nthcdr n x))
              (< (nfix n) (len x)))))

(local (defthm car-of-nthcdr
         (equal (car (nthcdr n x))
                (nth n x))))

(local (defthm cdr-of-nthcdr
         (equal (cdr (nthcdr n x))
                (nthcdr n (cdr x)))))

(defthm vals-is-nthcdr
  (implies (true-listp top)
           (equal (vals n top)
                  (nthcdr n top)))
  :hints (("goal" :induct (vals n top)
           :in-theory (enable equal-of-cons)
           ;; :expand ((nthcdr n top)
           ;;          (nthcdr (+ -1 n) (cdr top)))
           )))




(defun top-test ()
  (with-local-stobj top
    (mv-let (ans top)
      (let* ((vals0 (vals 0 top))
             (top (resize-subs 1 top))
             (vals1 (vals 0 top))
             (top (stobj-let ((sub$c (subsi 0 top)))
                             (sub$c)
                             (update-fld0$c 5 sub$c)
                             top))
             (vals2 (vals 0 top))
             (top (resize-subs 2 top))
             (vals3 (vals 0 top))
             (top (stobj-let ((sub$c (subsi 1 top)))
                             (sub$c)
                             (update-fld0$c 8 sub$c)
                             top))
             (vals4 (vals 0 top))
             (top (foo 0 1 top))
             (vals5 (vals 0 top))
             (top (foo 1 0 top))
             (vals6 (vals 0 top)))
        (mv (list vals0 vals1 vals2 vals3 vals4 vals5 vals6) top))
      ans)))

(make-event
 (let ((top-test-val (top-test)))
   `(defthm top-test-logic
      (equal (top-test) ',top-test-val)
      :hints(("Goal" :in-theory (set-difference-theories
                                 (current-theory :here)
                                 (executable-counterpart-theory :here)))))))

; Test invariant-risk detection using a program-mode wrapper.

(defun foo-program-wrapper (n m top)
  (declare (xargs :mode :program :stobjs top))
  (foo n m top))

(defun foo-program-wrapper-test-1 (i j)
  (declare (xargs :mode :program))
  (with-local-stobj top
    (mv-let (ans top)
      (let* ((top (resize-subs (1+ (max i j)) top))
             (top (stobj-let ((sub$c (subsi i top)))
                             (sub$c)
                             (update-fld0$c 10 sub$c)
                             top))
             (top (stobj-let ((sub$c (subsi j top)))
                             (sub$c)
                             (update-fld0$c 20 sub$c)
                             top))
             (old-vals (vals 0 top))
             (top (foo-program-wrapper i j top))
             (new-vals (vals 0 top)))
        (mv (list (list (nth i old-vals) (nth j old-vals))
                  (list (nth i new-vals) (nth j new-vals)))
            top))
      ans)))

(assert! (equal (foo-program-wrapper-test-1 0 1)
                '((10 20) (21 12))))

; Invariant-risk catches this error:
(must-fail (value (foo-program-wrapper-test-1 1 1))
           :expected :hard)

(defun read-only-stobj-let-test (i j)
  (declare (xargs :mode :program))
  (with-local-stobj top
    (mv-let (val1 val2 top)
      (let ((top (resize-subs (1+ (max i j)) top)))
        (stobj-let ((sub1$c (subsi i top))
                    (sub2$c (subs2i j top)))
                   (val1 val2)
                   (mv (fld0$c sub1$c)
                       (fld0$c sub2$c))
                   (mv val1 val2 top)))
      (list val1 val2))))

; There is no need to mark the function defined just above with invariant-risk.

(assert! (equal (getpropc 'read-only-stobj-let-test 'invariant-risk)
                nil))

(assert! (equal (read-only-stobj-let-test 1 1)
                '(nil nil)))

; Let's see now that there is no invariant-risk when the operation in question
; doesn't resize.

(defun update-top-at-0-to-3 (top)
  (declare (xargs :stobjs top
                  :guard (< 0 (subs-length top))))
  (stobj-let ((sub$c (subsi 0 top)))
             (sub$c)
             (update-fld0$c 3 sub$c)
             top))

(defun read-only-stobj-let-test-2 (i j top)
  (declare (xargs :mode :program :stobjs top))
  (stobj-let ((sub1$c (subsi i top))
              (sub2$c (subs2i j top)))
             (val1 val2)
             (mv (fld0$c sub1$c)
                 (fld0$c sub2$c))
             (cons val1 val2)))

(make-event (er-progn (trans-eval-no-warning '(let ((top (resize-subs 2 top)))
                                                (update-top-at-0-to-3 top))
                                             'my-test state nil)
                      (value '(value-triple t))))

(assert! (equal (read-only-stobj-let-test-2 0 0 top)
                '(3 . 3)))
