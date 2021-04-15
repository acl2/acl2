; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann (October, 2015)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See install-not-normalized.lisp.

(in-package "ACL2")

(include-book "install-not-normalized")

(local (include-book "std/testing/must-fail" :dir :system))
(local (include-book "std/testing/must-succeed" :dir :system))

(defmacro my-test (&rest forms)
  `(local (encapsulate
            ()
            (local (in-theory (current-theory :here))) ; avoid redundancy
            (local (progn ,@forms)))))

; Example (challenge supplied by Eric Smith):

(my-test

(defun return-nil (x) (declare (ignore x)) nil)

(defun foo (x) (return-nil x))

(must-fail
 (fn-is-body foo
             :hints (("Goal" :in-theory '(foo)))))

(must-fail
 (fn-is-body foo
             :hints (("Goal"
                      :expand ((foo x))
                      :in-theory (theory 'minimal-theory)))))

(install-not-normalized foo)

(must-succeed
 (fn-is-body foo
             :hints (("Goal" :in-theory '(foo$not-normalized)))))

(must-succeed
 (fn-is-body foo
             :hints (("Goal"
                      :expand ((foo x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with the default name supplied explicitly.

(my-test

(defun return-nil (x) (declare (ignore x)) nil)

(defun foo (x) (return-nil x))

(install-not-normalized foo :defthm-name 'foo$not-normalized)

(must-succeed
 (fn-is-body foo
             :hints (("Goal" :in-theory '(foo$not-normalized)))))

(must-succeed
 (fn-is-body foo
             :hints (("Goal"
                      :expand ((foo x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with a name supplied explicitly that is not the default.

(my-test

(defun return-nil (x) (declare (ignore x)) nil)

(defun foo (x) (return-nil x))

(install-not-normalized foo :defthm-name 'foo-is-unnormalized-body)

(must-succeed
 (fn-is-body foo
             :hints (("Goal" :in-theory '(foo-is-unnormalized-body)))))

(must-succeed
 (fn-is-body foo
             :hints (("Goal"
                      :expand ((foo x))
                      :in-theory (theory 'minimal-theory)))))
)

; Recursion example:

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(defun f-norm (x)
  (if (my-t)
      (if (consp x)
          (cons (car x) (f-norm (cdr x)))
        (my-zero))
    (my-nil)))

(must-fail
 (fn-is-body f-norm
             :hints (("Goal" :in-theory '(f-norm)))))

(must-fail
 (fn-is-body f-norm
             :hints (("Goal"
                      :expand ((f-norm x))
                      :in-theory (theory 'minimal-theory)))))

(install-not-normalized f-norm)

(must-succeed
 (fn-is-body f-norm
             :hints (("Goal" :in-theory '(f-norm$not-normalized)))))

(must-succeed
 (fn-is-body f-norm
             :hints (("Goal"
                      :expand ((f-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with the default name supplied explicitly.

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(defun f-norm (x)
  (if (my-t)
      (if (consp x)
          (cons (car x) (f-norm (cdr x)))
        (my-zero))
    (my-nil)))

(install-not-normalized f-norm :defthm-name 'f-norm$not-normalized)

(must-succeed
 (fn-is-body f-norm
             :hints (("Goal" :in-theory '(f-norm$not-normalized)))))

(must-succeed
 (fn-is-body f-norm
             :hints (("Goal"
                      :expand ((f-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with a name supplied explicitly that is not the default.

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(defun f-norm (x)
  (if (my-t)
      (if (consp x)
          (cons (car x) (f-norm (cdr x)))
        (my-zero))
    (my-nil)))

(install-not-normalized f-norm :defthm-name 'f-norm-alt-def)

(must-succeed
 (fn-is-body f-norm
             :hints (("Goal" :in-theory '(f-norm-alt-def)))))

(must-succeed
 (fn-is-body f-norm
             :hints (("Goal"
                      :expand ((f-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; Mutual-recursion example:

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(mutual-recursion

 (defun f1-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f2-norm (cdr x)))
         (my-zero))
     (my-nil)))

 (defun f2-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f1-norm (cdr x)))
         (my-zero))
     (my-nil)))
 )

(must-fail
 (fn-is-body f1-norm
             :hints (("Goal" :in-theory '(f1-norm)))))

(must-fail
 (fn-is-body f1-norm
             :hints (("Goal"
                      :expand ((f1-norm x))
                      :in-theory (theory 'minimal-theory)))))

(install-not-normalized f1-norm)

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal" :in-theory '(f1-norm$not-normalized)))))

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal"
                      :expand ((f1-norm x))
                      :in-theory (theory 'minimal-theory)))))

; f2 is handled too:

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal" :in-theory '(f2-norm$not-normalized)))))

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal"
                      :expand ((f2-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with one default name supplied explicitly.

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(mutual-recursion

 (defun f1-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f2-norm (cdr x)))
         (my-zero))
     (my-nil)))

 (defun f2-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f1-norm (cdr x)))
         (my-zero))
     (my-nil)))
 )

(install-not-normalized f1-norm :defthm-name 'f1-norm$not-normalized)

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal" :in-theory '(f1-norm$not-normalized)))))

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal"
                      :expand ((f1-norm x))
                      :in-theory (theory 'minimal-theory)))))

; f2 is handled too:

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal" :in-theory '(f2-norm$not-normalized)))))

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal"
                      :expand ((f2-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with a name supplied explicitly that is not the default.

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(mutual-recursion

 (defun f1-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f2-norm (cdr x)))
         (my-zero))
     (my-nil)))

 (defun f2-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f1-norm (cdr x)))
         (my-zero))
     (my-nil)))
 )

(install-not-normalized f1-norm :defthm-name 'f1-norm-new-def)

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal" :in-theory '(f1-norm-new-def)))))

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal"
                      :expand ((f1-norm x))
                      :in-theory (theory 'minimal-theory)))))

; f2 is handled too:

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal" :in-theory '(f2-norm$not-normalized)))))

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal"
                      :expand ((f2-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with both names supplied explicitly that are not the default.

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(mutual-recursion

 (defun f1-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f2-norm (cdr x)))
         (my-zero))
     (my-nil)))

 (defun f2-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f1-norm (cdr x)))
         (my-zero))
     (my-nil)))
 )

(install-not-normalized f1-norm :defthm-name '((f1-norm f1-norm-new-def)
                                               (f2-norm f2-norm-new-def)))

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal" :in-theory '(f1-norm-new-def)))))

(must-succeed
 (fn-is-body f1-norm
             :hints (("Goal"
                      :expand ((f1-norm x))
                      :in-theory (theory 'minimal-theory)))))

; f2 is handled too:

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal" :in-theory '(f2-norm-new-def)))))

(must-succeed
 (fn-is-body f2-norm
             :hints (("Goal"
                      :expand ((f2-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; Mutual-recursion example, but handling only one function in the nest:

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(mutual-recursion

 (defun f3-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f4-norm (cdr x)))
         (my-zero))
     (my-nil)))

 (defun f4-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f3-norm (cdr x)))
         (my-zero))
     (my-nil)))
 )

(must-fail
 (fn-is-body f3-norm
             :hints (("Goal" :in-theory '(f3-norm)))))

(must-fail
 (fn-is-body f3-norm
             :hints (("Goal"
                      :expand ((f3-norm x))
                      :in-theory (theory 'minimal-theory)))))

(install-not-normalized f3-norm :allp nil) ; "nil" for "not the entire nest

(must-succeed
 (fn-is-body f3-norm
             :hints (("Goal" :in-theory '(f3-norm$not-normalized)))))

(must-succeed
 (fn-is-body f3-norm
             :hints (("Goal"
                      :expand ((f3-norm x))
                      :in-theory (theory 'minimal-theory)))))

; F4 is not handled, since we gave nestp = nil in the call above of
; install-not-normalized.

(must-fail
 (fn-is-body f4-norm
             :hints (("Goal" :in-theory '(f4-norm$not-normalized)))))

(must-fail
 (fn-is-body f4-norm
             :hints (("Goal"
                      :expand ((f4-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; As above, but with a name supplied explicitly that is not the default.

(my-test

(defun my-t () t)
(defun my-nil () nil)
(defun my-zero () 0)

(mutual-recursion

 (defun f3-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f4-norm (cdr x)))
         (my-zero))
     (my-nil)))

 (defun f4-norm (x)
   (if (my-t)
       (if (consp x)
           (cons (car x) (f3-norm (cdr x)))
         (my-zero))
     (my-nil)))
 )

(install-not-normalized f3-norm
                        :allp nil ; "nil" for "not the entire nest
                        :defthm-name 'f3-norm-new)

(must-succeed
 (fn-is-body f3-norm
             :hints (("Goal" :in-theory '(f3-norm-new)))))

(must-succeed
 (fn-is-body f3-norm
             :hints (("Goal"
                      :expand ((f3-norm x))
                      :in-theory (theory 'minimal-theory)))))

; F4 is not handled, since we gave nestp = nil in the call above of
; install-not-normalized.

(must-fail
 (fn-is-body f4-norm
             :hints (("Goal" :in-theory '(f4-norm$not-normalized)))))

(must-fail
 (fn-is-body f4-norm
             :hints (("Goal"
                      :expand ((f4-norm x))
                      :in-theory (theory 'minimal-theory)))))
)

; Test :enable option, first showing that default of :auto can disable.

(my-test

(defun f5 (x)
  (cons x x))
(defun g5 (x)
  (car (f5 x)))
(defthm g5-identity
  (equal (g5 x) x))
(in-theory (disable f5 g5))
; Succeeds:
(thm (equal (g5 a) a))
(install-not-normalized g5)
; Succeeds because :enable option is :auto by default.
(thm (equal (g5 a) a))
(in-theory (enable g5$not-normalized))
; Fails now, showing the importance of :auto.
(must-fail
 (thm (equal (g5 a) a)))
)

; Identical to the above, but with explicit :enable :auto.

(my-test

(defun f5 (x)
  (cons x x))
(defun g5 (x)
  (car (f5 x)))
(defthm g5-identity
  (equal (g5 x) x))
(in-theory (disable f5 g5))
; Succeeds:
(thm (equal (g5 a) a))
(install-not-normalized g5 :enable :auto)
; Succeeds because :enable option is :auto by default.
(thm (equal (g5 a) a))
(in-theory (enable g5$not-normalized))
; Fails now, showing the importance of :auto.
(must-fail
 (thm (equal (g5 a) a)))
)

; Similar to preceding test, but with explicit :enable nil.

(my-test

(defun f5 (x)
  (cons x x))
(defun g5 (x)
  (car (f5 x)))
(defthm g5-identity
  (equal (g5 x) x))
(in-theory (disable f5 g5))
; Succeeds:
(thm (equal (g5 a) a))
(install-not-normalized g5 :enable nil)
(thm (equal (g5 a) a))
)

; Similar to preceding test, but with explicit :enable t.

(my-test

(defun f5 (x)
  (cons x x))
(defun g5 (x)
  (car (f5 x)))
(defthm g5-identity
  (equal (g5 x) x))
(in-theory (disable f5 g5))
; Succeeds:
(thm (equal (g5 a) a))
(install-not-normalized g5 :enable t)
(must-fail ; need g5$not-normalized to be disabled
 (thm (equal (g5 a) a)))
)

; This variant of the preceding tests illustrates that it is the disabled
; status of the original definition of the function that matters, not of
; other associated runes.

(my-test

(defun f5 (x)
  (cons x x))
(defun g5 (x)
  (car (f5 x)))
(defthm g5-identity
  (equal (g5 x) x))
(in-theory (disable f5 g5))
; Succeeds:
(thm (equal (g5 a) a))
(in-theory (e/d ((:d g5))
                ((:e g5) (:t g5))))
(install-not-normalized g5)
(must-fail ; need g5$not-normalized to be disabled
 (thm (equal (g5 a) a)))
)
