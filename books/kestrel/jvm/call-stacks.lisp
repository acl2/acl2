; Call stacks
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Note: Portions of this file may be taken from books/models/jvm/m5.  See the
; LICENSE file and authorship information there as well.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "frames")
(include-book "kestrel/sequences/defforall" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))

(defforall-simple framep)
(verify-guards acl2::all-framep)

(defund empty-call-stack () (declare (xargs :guard t)) nil)

;;TODO: build a tool to support defining typed stacks.

(defund call-stackp (stack) (declare (xargs :guard t)) (and (true-listp stack)
                                                            ;; (acl2::all-framep stack) ;;todo: put back (search for all-framep-change for other changes)
                                                            ))

(defthm call-stackp-of-empty-call-stack
  (call-stackp (empty-call-stack)))

(defund call-stack-size (stack)
  (declare (xargs :guard (call-stackp stack) :guard-hints (("Goal" :in-theory (enable call-stackp)))))
  (len stack))

;; keep enabled.
(defun empty-call-stackp (stack)
  (declare (xargs :guard (call-stackp stack) :guard-hints (("Goal" :in-theory (enable call-stackp)))))
  (equal 0 (call-stack-size stack)))

;fixme should be types for the different uses (e.g., for the call stack, obj must be a framep)
(defund push-frame (obj stack)
 (declare (xargs :guard (and (call-stackp stack) (framep obj))))
 (cons obj stack))

;guard to require a non-empty-stack?
(defund top-frame (stack) ;fixme guard should require non-empty
  (declare (xargs :guard (call-stackp stack) :guard-hints (("Goal" :in-theory (enable call-stackp)))))
  (car stack))

;guard to require a non-empty-stack?
(defund pop-frame (stack)
  (declare (xargs :guard (call-stackp stack) :guard-hints (("Goal" :in-theory (enable call-stackp)))))
  (cdr stack))

(defthm all-framep-of-pop-frame
  (implies (acl2::all-framep frames)
           (acl2::all-framep (pop-frame frames)))
  :hints (("Goal" :in-theory (enable acl2::all-framep pop-frame))))

(defthm acl2-numberp-of-call-stack-size
  (equal (acl2-numberp (call-stack-size stack))
         t))

(defthm top-frame-of-push-frame
  (equal (top-frame (push-frame frame stack))
         frame)
  :hints (("Goal" :in-theory (enable top-frame push-frame))))

(defthm pop-frame-of-push-frame
  (equal (pop-frame (push-frame frame stack))
         stack)
  :hints (("Goal" :in-theory (enable pop-frame push-frame))))

;; (defthm empty-call-stackp-of-push-frame
;;   (equal (empty-call-stackp (push-frame frame stack))
;;          nil)
;;     :hints (("Goal" :in-theory (enable empty-call-stackp push-frame))))

;; (defthm empty-call-stackp-of-pop-frame
;;   (equal (empty-call-stackp (pop-frame stack))
;;          (not (< 1 (call-stack-size stack))))
;;   :hints (("Goal" :in-theory (enable empty-call-stackp pop-frame CALL-STACK-SIZE))))

(defthm call-stack-size-of-pop-frame
  (implies (and (not (empty-call-stackp stack))
      ;          (stackp stack)
                )
           (equal (call-stack-size (pop-frame stack))
                  (+ -1 (call-stack-size stack))))
  :hints (("Goal" :in-theory (enable call-stack-size pop-frame empty-call-stackp call-stackp))))

(defthm call-stack-size-of-push-frame
  (equal (call-stack-size (push-frame frame stack))
         (+ 1 (call-stack-size stack)))
  :hints (("Goal" :in-theory (enable call-stack-size push-frame))))

(defthm call-stackp-of-push-frame
  (equal (call-stackp (push-frame frame stack))
         (and (call-stackp stack)
              ;; (framep frame) ;all-framep-change
              ))
  :hints (("Goal" :in-theory (enable call-stackp push-frame))))

(defthm call-stackp-of-pop-frame
  (implies (call-stackp stack)
           (call-stackp (pop-frame stack)))
  :hints (("Goal" :in-theory (enable call-stackp pop-frame))))

(defthm x-equals-push-frame-pop-frame-x-rewrite
  (equal (equal x (push-frame obj (pop-frame x)))
         (and (consp x)
              (equal obj (top-frame x))))
  :hints (("Goal" :in-theory (enable push-frame pop-frame top-frame))))

(defthm x-equals-push-operand-pop-operand-x-rewrite
  (equal (equal x (push-operand obj (pop-operand x)))
         (and (consp x)
              (equal obj (top-frame x))))
  :hints (("Goal" :in-theory (enable push-operand pop-operand top-frame))))

;;; todo: clean these up:

;i guess the order here matters?
;just for efficiency (call-stack-size-of-push and the constant collection rule would be sufficient but slower)
(defthm call-stack-size-of-push-frame-of-push-frame
  (equal (call-stack-size (push-frame item2 (push-frame item stack)))
         (+ 2 (call-stack-size stack))))

;again, just for efficiency
;more like this?
(defthm call-stack-size-of-push-frame-of-push-frame-of-push-frame
  (equal (call-stack-size (push-frame item3 (push-frame item2 (push-frame item stack))))
         (+ 3 (call-stack-size stack))))

(defthm call-stack-size-of-push-frame-of-push-frame-of-push-frame-of-push-frame
  (equal (call-stack-size (push-frame item4 (push-frame item3 (push-frame item2 (push-frame item stack)))))
         (+ 4 (call-stack-size stack))))

(defthm call-stack-size-of-pop-frame-strong
  (equal (call-stack-size (pop-frame stack))
         (if (equal (call-stack-size stack) 0)
             0
           (+ -1 (call-stack-size stack))))
  :hints (("Goal" :in-theory (enable pop-frame call-stack-size))))

(defthm call-stack-size-lemma
  (equal (< (+ 1 (call-stack-size (pop-frame (pop-frame x))))
            (call-stack-size x))
         (< 1 (call-stack-size x))))

;; special case of arithmetic cancellation
;gen the 0?
(defthm equal-of-+-of-call-stack-size-combine-constants
  (implies (and (syntaxp (quotep k1))
                (syntaxp (quotep k2)))
           (equal (equal k1 (+ k2 (call-stack-size call-stack)))
                  (and (acl2-numberp k1)
                       (equal (- k1 k2) (call-stack-size call-stack))))))

(defthm not-equal-of-call-stack-size-and-constant-when-negative
  (implies (and (syntaxp (quotep k))
                (< k 0))
           (not (equal k (call-stack-size call-stack)))))

(defthm one-plus-call-stack-size-hack
  (not (equal (+ 1 (call-stack-size x)) 0)))

;; ;which form do we prefer?
;; (defthm equal-of-call-stack-size-and-0
;;   (equal (empty-call-stackp call-stack)
;;          (equal (call-stack-size call-stack) 0))
;;   :hints (("Goal" :in-theory (enable empty-call-stackp call-stack-size))))

(defthmd <-of-call-stack-size-and-plus-of-call-stack-size-of-pop-frame
  (implies (and (syntaxp (quotep k))
                (<= 2 k))
           (< (call-stack-size x)
              (+ k (call-stack-size (pop-frame x)))))
  :hints (("Goal" :in-theory (enable call-stack-size pop-frame))))

;needed?
(defthm equal-of-push-frame-and-push-frame
  (equal (equal (push-frame val1 stack1)
                (push-frame val2 stack2))
         (and (equal val1 val2)
              (equal stack1 stack2)))
  :hints (("Goal" :in-theory (enable push-frame))))

(defthm myif-of-push-frame-and-push-frame
  (equal (myif test (push-frame x1 y1) (push-frame x2 y2))
         (push-frame (myif test x1 x2)
                     (myif test y1 y2)))
  :hints (("Goal" :in-theory (enable myif))))

;move
(defthm acl2::empty-call-stackp-redef
  (equal (jvm::empty-call-stackp call-stack)
         (equal 0 (jvm::call-stack-size call-stack)))
  :hints (("Goal" :in-theory (enable jvm::empty-call-stackp jvm::call-stack-size))))

;move
(defthm acl2::all-framep-of-pop-frame
  (implies (and (acl2::all-framep call-stack)
                (jvm::call-stackp call-stack)
                (not (jvm::empty-call-stackp call-stack)))
           (acl2::all-framep (jvm::pop-frame call-stack)))
  :hints (("Goal" :in-theory (enable jvm::pop-frame acl2::all-framep jvm::empty-call-stackp))))
