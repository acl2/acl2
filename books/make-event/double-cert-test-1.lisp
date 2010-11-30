(in-package "ACL2")

(make-event
 (progn (defttag :my-ttag)
        (progn! (let ((val (sys-call "pwd" nil)))
                  (value (list 'defun 'foo () val))))))

(defthm just-a-test
  (equal (foo) nil))
