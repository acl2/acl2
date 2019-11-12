; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "FGL")

(include-book "stack")

(define stack-push-scratch-list-aux ((x scratchlist-p)
                                     stack)
  :guard-hints (("goal" :in-theory (enable stack$a-push-scratch)
                 :expand ((:free (stack) (stack-push-scratch-list-aux (cdr x) stack)))))
  (mbe :logic (non-exec (b* (((major-frame jframe) (car stack))
                             ((minor-frame nframe) (car jframe.minor-stack)))
                          (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                                                     (cons (change-minor-frame nframe
                                                                                               :scratch (revappend x nframe.scratch))
                                                                           (cdr jframe.minor-stack)))
                                                 (cdr stack)))))
       :exec
       (if (atom x)
           stack
         (b* ((stack (stack-push-scratch (car x) stack)))
           (stack-push-scratch-list-aux (cdr x) stack)))))

(define stack-push-scratch-list ((x scratchlist-p)
                                 stack)
  :guard-hints (("goal" :in-theory (enable stack-push-scratch-list-aux)))
  (mbe :logic (non-exec (b* (((major-frame jframe) (car stack))
                             ((minor-frame nframe) (car jframe.minor-stack)))
                          (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                                                     (cons (change-minor-frame nframe
                                                                                               :scratch (append x nframe.scratch))
                                                                           (cdr jframe.minor-stack)))
                                                 (cdr stack)))))
       :exec (stack-push-scratch-list-aux (rev x) stack)))

(define stack-pop-n-scratch ((n natp)
                             stack)
  :guard (<= n (stack-scratch-len stack))
  :guard-hints (("goal" :in-theory (enable stack$a-pop-scratch
                                           stack$a-scratch-len)
                 :expand ((:free (stack) (stack-pop-n-scratch (+ -1 n) stack)))))
  (mbe :logic (non-exec (b* (((major-frame jframe) (car stack))
                             ((minor-frame nframe) (car jframe.minor-stack)))
                          (major-stack-fix (cons (change-major-frame jframe :minor-stack
                                                                     (cons (change-minor-frame nframe
                                                                                               :scratch (nthcdr n nframe.scratch))
                                                                           (cdr jframe.minor-stack)))
                                                 (cdr stack)))))
       :exec (if (zp n)
                 stack
               (b* ((stack (stack-pop-scratch stack)))
                 (stack-pop-n-scratch (1- n) stack)))))

(local (defthm nthcdr-by-len-when-true-listp
         (implies (true-listp x)
                  (equal (nthcdr (len x) x) nil))))
(local (defthm true-listp-when-scratchlist-p-rw
         (implies (scratchlist-p x)
                  (true-listp x))))

(define stack-import-minor-frame ((x minor-frame-p)
                                  stack)
  :guard-hints (("goal" :in-theory (enable stack$a-set-minor-bindings
                                           stack$a-set-term
                                           stack$a-set-term-index
                                           stack$a-scratch-len
                                           stack-pop-n-scratch
                                           stack-push-scratch-list)))
  :prepwork ()
  (mbe :logic (non-exec (b* (((major-frame jframe) (car stack)))
                          (major-stack-fix (cons (change-major-frame jframe
                                                                     :minor-stack
                                                                     (cons (minor-frame-fix x)
                                                                           (cdr jframe.minor-stack)))
                                                 (cdr stack)))))
       :exec (b* (((minor-frame x))
                  (stack (stack-set-minor-bindings x.bindings stack))
                  (stack (stack-set-term x.term stack))
                  (stack (stack-set-term-index x.term-index stack))
                  (stack (stack-pop-n-scratch (stack-scratch-len stack) stack)))
               (stack-push-scratch-list x.scratch stack))))

(define stack-import-minor-frames-aux ((x minor-stack-p)
                                     stack)
  :guard-hints (("goal" :in-theory (enable stack-import-minor-frame
                                           stack$a-push-minor-frame)
                 :expand ((:free (stack) (stack-import-minor-frames-aux (cdr x) stack)))))
  (mbe :logic (non-exec (b* (((major-frame jframe) (car stack)))
                          (major-stack-fix
                           (cons (change-major-frame jframe
                                                     :minor-stack (revappend x
                                                                             (cdr jframe.minor-stack)))
                                 (cdr stack)))))
       :exec (b* ((stack (stack-import-minor-frame (car x) stack))
                  ((unless (consp (cdr x))) stack)
                  (stack (stack-push-minor-frame stack)))
               (stack-import-minor-frames-aux (cdr x) stack))))

(local (defthm minor-stack-p-of-rev
         (implies (minor-stack-p x)
                  (minor-stack-p (rev x)))
         :hints(("Goal" :in-theory (enable rev minor-stack-p) 
                 :induct (minor-stack-p x)))))


(define stack-import-minor-frames ((x minor-stack-p)
                                 stack)
  :guard-hints (("goal" :in-theory (enable stack-import-minor-frames-aux)))
  (mbe :logic (non-exec (b* (((major-frame jframe) (car stack)))
                          (major-stack-fix
                           (cons (change-major-frame jframe
                                                     :minor-stack (append x
                                                                          (cdr jframe.minor-stack)))
                                 (cdr stack)))))
       :exec (stack-import-minor-frames-aux (rev x) stack)))

(define stack-pop-n-minor-frames ((n natp)
                                  stack)
  :guard (< n (stack-minor-frames stack))
  :guard-hints (("goal" :in-theory (enable stack$a-pop-minor-frame
                                           stack$a-minor-frames
                                           stack-pop-n-scratch
                                           stack$a-scratch-len)
                 :expand ((:free (stack) (stack-pop-n-minor-frames (+ -1 n) stack)))))
  (mbe :logic (non-exec (b* (((major-frame jframe) (car stack))
                             ((minor-frame nframe) (car jframe.minor-stack)))
                          (major-stack-fix (cons (change-major-frame jframe :minor-stack (nthcdr n jframe.minor-stack))
                                                 (cdr stack)))))
       :exec (if (zp n)
                 stack
               (b* ((stack (stack-pop-n-scratch (stack-scratch-len stack) stack))
                    (stack (stack-pop-minor-frame stack)))
                 (stack-pop-n-minor-frames (1- n) stack)))))

(local (defthm len-when-minor-stack-p
         (implies (minor-stack-p x)
                  (< 0 (len x)))
         :rule-classes :linear))


(define stack-import-major-frame ((x major-frame-p)
                                  stack)
  :guard-hints (("goal" :in-theory (enable stack$a-set-bindings
                                           stack$a-set-rule
                                           stack$a-set-phase
                                           stack-pop-n-minor-frames
                                           stack-import-minor-frames
                                           stack$a-minor-frames)))
  :prepwork ((local (defthm nthcdr-by-len-minus-one
                      (implies (and (true-listp x)
                                    (consp x))
                               (equal (nthcdr (+ -1 (len x)) x)
                                      (list (car (last x)))))))
             (local (defthm true-listp-when-minor-stack-p-rw
                      (implies (minor-stack-p x)
                               (true-listp x)))))
  (mbe :logic (non-exec (major-stack-fix (cons x
                                               (cdr stack))))
       :exec (b* (((major-frame x))
                  (stack (stack-set-bindings x.bindings stack))
                  (stack (stack-set-rule x.rule stack))
                  (stack (stack-set-phase x.phase stack))
                  (stack (stack-pop-n-minor-frames (1- (stack-minor-frames stack)) stack)))
               (stack-import-minor-frames x.minor-stack stack))))

(define stack-import-major-frames-aux ((x major-stack-p)
                                   stack)
  :guard-hints (("goal" :in-theory (enable stack-import-major-frame
                                           stack$a-push-frame)
                 :expand ((:free (stack) (stack-import-major-frames-aux (cdr x) stack)))))
  (mbe :logic (non-exec (major-stack-fix (revappend x (cdr stack))))
       :exec (b* ((stack (stack-import-major-frame (car x) stack))
                  ((unless (consp (cdr x))) stack)
                  (stack (stack-push-frame stack)))
               (stack-import-major-frames-aux (cdr x) stack))))

(local (defthm major-stack-p-of-rev
         (implies (major-stack-p x)
                  (major-stack-p (rev x)))
         :hints(("Goal" :in-theory (enable rev major-stack-p) 
                 :induct (major-stack-p x)))))

(define stack-import-major-frames ((x major-stack-p)
                                   stack)
  :guard-hints(("Goal" :in-theory (enable stack-import-major-frames-aux)))
  (mbe :logic (non-exec (major-stack-fix (append x (cdr stack))))
       :exec (stack-import-major-frames-aux (rev x) stack)))

(local (defthm len-cdr-when-consp
         (implies (consp x)
                  (equal (len (cdr x)) (+ -1 (len x))))))

(local (defthm nthcdr-of-nil
         (equal (nthcdr n nil) nil)))

(local (defthm len-nthcdr
         (equal (len (nthcdr n x))
                (nfix (- (len x) (nfix n))))))

(define stack-pop-n-major-frames ((n natp)
                                  stack)
  :guard (< n (stack-frames stack))
  :guard-hints (("goal" :in-theory (enable stack$a-pop-frame
                                           stack$a-frames
                                           stack-pop-n-minor-frames
                                           stack$a-minor-frames
                                           stack-pop-n-scratch
                                           stack$a-scratch-len)
                 :expand ((:free (stack) (stack-pop-n-major-frames (+ -1 n) stack)))))
  (mbe :logic (non-exec (major-stack-fix (nthcdr n stack)))
       :exec (if (zp n)
                 stack
               (b* ((stack (stack-pop-n-minor-frames (1- (stack-minor-frames stack)) stack))
                    (stack (stack-pop-n-scratch (stack-scratch-len stack) stack))
                    (stack (stack-pop-frame stack)))
                 (stack-pop-n-major-frames (1- n) stack)))))

(local (defthm consp-when-major-stack-p
         (implies (major-stack-p x)
                  (consp x))
         :rule-classes :forward-chaining))

(define stack-import ((x major-stack-p) stack)
  :enabled t
  :guard-hints (("goal" :in-theory (enable stack-pop-n-major-frames
                                           stack-import-major-frames
                                           stack$a-frames)))
  :prepwork ((local (defthm nthcdr-by-len-minus-one
                      (implies (and (true-listp x)
                                    (consp x))
                               (equal (nthcdr (+ -1 (len x)) x)
                                      (list (car (last x)))))))
             (local (defthm true-listp-when-major-stack-p-rw
                      (implies (major-stack-p x)
                               (true-listp x)))))
  (mbe :logic (non-exec (major-stack-fix x))
       :exec (b* ((stack (stack-pop-n-major-frames (1- (stack-frames stack)) stack)))
               (stack-import-major-frames x stack))))
