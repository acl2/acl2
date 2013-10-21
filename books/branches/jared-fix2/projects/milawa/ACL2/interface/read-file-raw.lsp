;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CL-USER")

(defmacro report-time (message form)
  `(let* ((start-time (get-internal-real-time))
          (value      ,form)
          (stop-time  (get-internal-real-time))
          (elapsed    (/ (coerce (- stop-time start-time) 'float)
                         internal-time-units-per-second)))
     (format t ";; ~A took ~$ seconds~%" ,message elapsed)
     value))

(defvar *milawa-readtable* (copy-readtable *readtable*))
(declaim (readtable *milawa-readtable*))

(defvar *milawa-abbreviations-hash-table*)
(declaim (type hash-table *milawa-abbreviations-hash-table*))

(defun milawa-sharp-equal-reader (stream subchar arg)
  (declare (ignore subchar))
  (multiple-value-bind
   (value presentp)
   (gethash arg *milawa-abbreviations-hash-table*)
   (declare (ignore value))
   (when presentp
     (error "#~A= is already defined." arg))
   (let ((object (read stream)))
     (setf (gethash arg *milawa-abbreviations-hash-table*) object))))

(defun milawa-sharp-sharp-reader (stream subchar arg)
  (declare (ignore stream subchar))
  (or (gethash arg *milawa-abbreviations-hash-table*)
      (error "#~A# used but not defined." arg)))

(let ((*readtable* *milawa-readtable*))
  (set-dispatch-macro-character #\# #\# #'milawa-sharp-sharp-reader)
  (set-dispatch-macro-character #\# #\= #'milawa-sharp-equal-reader))

(defconstant unique-cons-for-eof (cons 'unique-cons 'for-eof))

(defun milawa-read-file-aux (stream)
   (let ((obj (read stream nil unique-cons-for-eof)))
     (cond ((eq obj unique-cons-for-eof)
            nil)
           (t
            (cons obj (milawa-read-file-aux stream))))))

(defun MILAWA::milawa-read-file (filename)
  (format t ";; Reading from ~A~%" filename)
  (report-time "Reading the file"
    (let* ((*milawa-abbreviations-hash-table* (make-hash-table
                                               :size 10000
                                               :rehash-size 100000
                                               :test 'eql))
           (*readtable* *milawa-readtable*)
           (*package*   (find-package "MILAWA"))
           (stream (open filename
                         :direction :input
                         :if-does-not-exist :error))
           (contents (milawa-read-file-aux stream)))
      (close stream)
      ;; the actual version of this for the proof checker includes
      ;; an acceptable-objectp check, but in this case we don't
      ;; really care.
      contents)))




