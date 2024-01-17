(in-package #:local-time.test)

(defun benchmark-belfast (&key (n 10000))
  "Europe/Belfast has a high number of transitions."
  (local-time::define-timezone belfast-tz
      (merge-pathnames
       #p"Europe/Belfast"
       local-time::*default-timezone-repository-path*)
    :load t)
  (let ((times nil)
        (transitions (local-time::timezone-transitions belfast-tz)))
    (map nil (lambda (transition)
               (push (1- transition) times)
               (push transition times)
               (push (1+ transition) times))
         transitions)
    (format t "Get ~D times ~D different unix-times on ~D transitions"
            n (length times) (length transitions))
    (time (dotimes (i n)
            (dolist (time times)
              (local-time::transition-position time transitions))))))
