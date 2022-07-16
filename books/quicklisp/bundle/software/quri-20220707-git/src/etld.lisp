(in-package :cl-user)
(defpackage quri.etld
  (:use :cl)
  (:import-from :alexandria
                :starts-with-subseq
                :ends-with-subseq)
  (:export :parse-domain))
(in-package :quri.etld)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *default-etld-names*
    #.(asdf:system-relative-pathname :quri #P"data/effective_tld_names.dat"))

  (defun load-etld-data (&optional (etld-names-file *default-etld-names*))
    (with-open-file (in etld-names-file
                        :element-type #+lispworks :default #-lispworks 'character
                        :external-format #+clisp charset:utf-8 #-clisp :utf-8)
      (loop with special-tlds = nil
         with normal-tlds = (make-hash-table :test 'equal)
         with wildcard-tlds = (make-hash-table :test 'equal)
         for line = (read-line in nil nil)
         while line
         unless (or (= 0 (length line))
                    (starts-with-subseq "//" line))
         do (cond
              ((starts-with-subseq "*" line)
               (setf (gethash (subseq line 2) wildcard-tlds) t))
              ((starts-with-subseq "!" line)
               (push (subseq line 1) special-tlds))
              (t
               (setf (gethash line normal-tlds) t)))
         finally (return (list normal-tlds wildcard-tlds special-tlds))))))

(defvar *etlds*
  #-abcl '#.(load-etld-data)
  #+abcl (load-etld-data))

(defun next-subdomain (hostname &optional (start 0))
  (let ((pos (position #\. hostname :start start)))
    (when pos
      (incf pos)
      (values (subseq hostname pos)
              pos))))

(defun make-subdomain-iter (hostname)
  (let ((current-pos 0)
        (first t))
    (lambda ()
      (block nil
        (when first
          (setq first nil)
          (return hostname))
        (multiple-value-bind (subdomain pos)
            (next-subdomain hostname current-pos)
          (when subdomain
            (setf current-pos pos)
            subdomain))))))

(defun parse-domain (hostname)
  (dolist (tld (third *etlds*))
    (when (ends-with-subseq tld hostname)
      (if (= (length tld) (length hostname))
          (return-from parse-domain hostname)
          (when (char= (aref hostname (- (length hostname) (length tld) 1))
                       #\.)
            (return-from parse-domain
              (subseq hostname
                      (- (length hostname) (length tld))))))))

  (loop with iter = (make-subdomain-iter hostname)
        with pre-prev-subdomain = nil
        with prev-subdomain = nil
        for subdomain = (funcall iter)
        while subdomain
        if (gethash subdomain (second *etlds*)) do
          (return pre-prev-subdomain)
        else if (gethash subdomain (first *etlds*)) do
          (return (if (string= subdomain hostname)
                      nil
                      prev-subdomain))
        do (setf pre-prev-subdomain prev-subdomain
                 prev-subdomain subdomain)
        finally
           (let* ((pos (position #\. hostname :from-end t))
                  (pos (and pos
                            (position #\. hostname :from-end t :end pos))))
             (return
               (if pos
                   (subseq hostname (1+ pos))
                   hostname)))))
