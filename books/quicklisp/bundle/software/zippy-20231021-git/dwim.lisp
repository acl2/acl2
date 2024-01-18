(defpackage #:org.shirakumo.zippy.dwim
  (:use #:cl)
  (:local-nicknames
   (#:zippy #:org.shirakumo.zippy)
   (#:file-attributes #:org.shirakumo.file-attributes))
  (:export #:compress))

(in-package #:org.shirakumo.zippy.dwim)

(defun file-executable-p (file)
  (with-open-file (stream file :element-type '(unsigned-byte 8))
    (let ((buffer (make-array 4 :element-type '(unsigned-byte 8))))
      (read-sequence buffer stream)
      (cond ((equalp buffer #(#xCF #xFA #xED #xFE)) :mach-o)
            ((equalp buffer #(#x7F #x45 #x4C #x46)) :elf)
            ((equalp buffer #(#x4D #x5A #x90 #x00)) :pe)))))

(defun entry-executable-p (entry)
  (let ((path (zippy:content entry)))
    (unless (pathname-utils:directory-p path)
      (and (not (find (pathname-type path) '("so" "dll" "dylib") :test #'string-equal))
           (file-executable-p path)))))

(defun compress (thing output)
  (format T "Scanning files...~%")
  (let ((archive (zippy::ensure-zip-file thing)))
    (loop for entry across (zippy:entries archive)
          do (when (entry-executable-p entry)
               (format T "~&Marking ~a as executable~%" (zippy:content entry))
               (setf (zippy:attributes entry)
                     (list '(:normal T) :unix
                           (file-attributes:encode-attributes
                            '(:OTHER-EXECUTE T :OTHER-WRITE T :OTHER-READ T :GROUP-EXECUTE T :GROUP-WRITE T
                              :GROUP-READ T :OWNER-EXECUTE T :OWNER-WRITE T :OWNER-READ T :STICKY NIL
                              :SET-GROUP NIL :SET-USER NIL :FIFO NIL :DEVICE NIL :DIRECTORY NIL :NORMAL T
                              :LINK NIL :SOCKET NIL)
                            :unix)))))
    (format T "Compressing...~%")
    (zippy:compress-zip archive output :if-exists :supersede)
    (format T "Done: ~a~%" (pathname-utils:native-namestring output))))

(defun parse-path (path)
  (probe-file (pathname-utils:parse-native-namestring path)))

(push :deploy-console *features*)

(defun main ()
  (destructuring-bind (self &rest args) (uiop:raw-command-line-arguments)
    (flet ((exit ()
             (unless (uiop:getenv "SHELL")
               (format T "Press key to close...~%")
               (read-line))))
      (cond ((rest args)
             (compress (mapcar #'parse-path (rest args))
                       (pathname-utils:parse-native-namestring (first args)))
             (exit))
            (args
             (compress (parse-path (first args))
                       (merge-pathnames "output.zip" self))
             (exit))
            (T
             (format T "Usage:
~a file-to-zip
~a zip-name file-to-zip...
"
                     self self))))))
