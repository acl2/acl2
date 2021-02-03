(in-package "ACL2")

;; This book contains examples / tests for bind-from-rules.

(include-book "bind-from-rules")
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (defthm integerp-when-unsigned-byte-p
    (implies (unsigned-byte-p freesize x) ;note the free var
             (integerp x)))

  ;; We constrain foo to return an unsigned-byte-p of size 16.
  (encapsulate (((foo *) => *))
    (local (defun foo (x) (declare (ignore x)) 0))
    (defthm usb16-of-foo
      (unsigned-byte-p 16 (foo x))))

  ;;It seems absurd that this fails.  ACL2 knows that foo always returns a
  ;;usb-16, and that every usb-16 is an integerp, but it can't put the two facts
  ;;together.
  (must-fail
   (defthm integerp-of-foo
     (integerp (foo x))))

  ;;Note the call of "bind-from-rules".
  ;;Not that this rule doesn't mention foo or the size 16, so it's fairly general.
  (defthm integerp-when-unsigned-byte-p2
    (implies (bind-from-rules (unsigned-byte-p (:free freesize) x))
             (integerp x)))

  ;; Test the new rule (disable tau just in case):

  ;;Now this works:
  (defthmd integerp-of-foo
    (integerp (foo x))
    :hints (("Goal" :in-theory (disable (:executable-counterpart tau-system)))))

  ;; This also works, even though we used y instead of x:
  (defthmd integerp-of-foo-2
    (integerp (foo y))
    :hints (("Goal" :in-theory (disable (:executable-counterpart tau-system)))))

  (defthmd integerp-of-foo-of-cons
    (integerp (foo (cons a b)))
    :hints (("Goal" :in-theory (disable (:executable-counterpart tau-system))))))

;; More complicated pattern (foo2 of bar)

(encapsulate
  ()
  (defthm integerp-when-unsigned-byte-p
    (implies (unsigned-byte-p freesize x) ;note the free var
             (integerp x)))

  ;; We constrain "foo2 of bar" to return an unsigned-byte-p of length 16.
  (encapsulate (((foo2 *) => *)
                ((bar *) => *))
    (local (defun foo2 (x) (declare (ignore x)) 0))
    (local (defun bar (x) (declare (ignore x)) 0))
    (defthm usb16-of-foo2-of-bar
      (unsigned-byte-p 16 (foo2 (bar x)))))

  ;; ;;It seems absurd that this fails.  ACL2 knows that foo2 always returns a
  ;; ;;usb-16, and that every usb-16 is an integerp, but it can't put the two facts
  ;; ;;together.
  ;; (defthm integerp-of-foo2
  ;;   (integerp (foo2 (bar x))))

  ;;Note the call of "bind-from-rules".
  ;;Not that this rule doesn't mention foo2 or bar.
  (defthm integerp-when-unsigned-byte-p2
    (implies (bind-from-rules (unsigned-byte-p (:free freesize) x))
             (integerp x)))

  ;;Now this works:
  (defthm integerp-of-foo2
    (integerp (foo2 (bar x)))))
