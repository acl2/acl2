; Shellpool - Interface from Common Lisp to External Programs
; Copyright (C) 2014-2015 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

; basic.lisp -- tests of basic return/output capture

(defun run-and-gather (cmd)
  "Runs command, gathering output, returns (values status stdout stderr)."
  (format t "** Running command ~s~%" cmd)
  (let* ((stdout nil)
         (stderr nil)
         (each-line (lambda (line type)
                      (format t "  (~s) ~s~%" type line)
                      (force-output)
                      (case type
                        (:stdout (push line stdout))
                        (:stderr (push line stderr))
                        (otherwise (error "Bad type ~s for line ~s~%" type line)))))
         (status (shellpool:run cmd :each-line each-line))
         (stdout (nreverse stdout))
         (stderr (nreverse stderr)))
    (values status stdout stderr)))

(defun check (name expected actual)
  (if (equal expected actual)
      (format t "OK ~a~%" name)
    (error "FAIL ~a: Expected ~s, Found ~s~%" name expected actual)))

(defun basic-test (cmd &key
                       (status '0)
                       (stdout 'nil)
                       (stderr 'nil))
  (multiple-value-bind
   (actual-status actual-stdout actual-stderr)
   (run-and-gather cmd)
   (check "status" status actual-status)
   (check "stdout" stdout actual-stdout)
   (check "stderr" stderr actual-stderr)))


; Trivial tests:

(basic-test "echo hello"
            :stdout '("hello"))

(basic-test "echo hello 1>&2 "
            :stderr '("hello"))

(basic-test "echo -n hello "
            :stdout '("hello"))

(basic-test "echo -n hello 1>&2 "
            :stderr '("hello"))

(basic-test "exit 1"
            :status 1)

(basic-test "exit 15"
            :status 15)


; This read test is meant to ensure that the subcommand really doesn't get any
; input stream attached to it.  Perhaps we would one day want to change how
; this works to allow hooking up streams to commands, but that seems pretty
; hard and scary.  What if they send Ctrl+D and end the stream or something?
; Could we lose our bash shell?

(basic-test "read -p 'Will this work?' yn"
            :status 1)


; Test some more complex output interleaving.

(basic-test "./test1.sh"
            :status 0
            :stdout '("stdout line 1" "stdout line 2" "stdout line 3")
            :stderr '("stderr line 1" "stderr line 2"))


; Like the previous test, but the output should be produced (and streamed)
; incrementally.  You should notice lag as the messages are printed, but you
; should see each message as it becomes available.

(basic-test "./test2.sh"
            :status 2
            :stdout '("stdout line 1" "stdout line 2" "stdout line 3")
            :stderr '("stderr line 1" "stderr line 2"))


; Now some tests of garbage commands.

(defun check-bad-input (cmd &key
                            (status '2)
                            (stdout 'nil))
  (multiple-value-bind
   (actual-status actual-stdout actual-stderr)
   (run-and-gather cmd)
   (check "status" status actual-status)
   (check "stdout" stdout actual-stdout)
   (or (consp actual-stderr)
       (error "Expected an error message."))))

(check-bad-input "echo \"oops, forgot ending quote")

; Now try to make sure that didn't screw up the shell somehow.
(basic-test "echo hello"
            :stdout '("hello"))

(check-bad-input "echo 'oops, forgot ending single quote")

; And try to make sure THAT didn't screw up the shell, either.
(basic-test "echo hello"
            :stdout '("hello"))

(check-bad-input "(echo \"Oops, no closing paren.\" ")

; And again, try to make sure that didn't screw up the shell.
(basic-test "echo hello"
            :stdout '("hello"))

;; (let* ((proc (ccl:run-program "./harness2.sh" nil
;;                               :wait nil
;;                               :input :stream
;;                               :output :stream
;;                               :error :stream))
;;        (stdout (ccl::external-process-output-stream proc))
;;        (stderr (ccl::external-process-output-stream proc)))
;;   (declare (ignorable stdout stderr))

;;   ;; (let ((foo (read-line stderr nil)))
;;   ;;   (format t "Got stderr line~s~%" foo)
;;   ;;   (force-output))

;;   (loop do
;;         (let ((line (read-line stdout nil)))
;;           (format t "Got line ~s~%" line)
;;           (force-output)
;;           (when (not line)
;;             (loop-finish)))))



(let ((oops nil))
  (format t "** Checking that starting too many shells doesn't work.~%")
  (handler-case
    (progn (shellpool:start 2000)
           (setq oops t))
    (error (condition)
           (declare (ignore condition))
           (format t "OK: Got error as expected.~%")
           nil))
  (when oops
    (error "Started 2000 shells?")))

(let ((oops nil))
  (format t "** Checking that ensure'ing too many shells doesn't work.~%")
  (handler-case
    (progn (shellpool:ensure 2000)
           (setq oops t))
    (error (condition)
           (declare (ignore condition))
           (format t "OK: Got error as expected.~%")
           nil))
  (when oops
    (error "Started 2000 shells?")))


