; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Portcullis: 
; Empty

; Copy-file

; (copy-file name1 name2 state) copies the file named name1 to a file named name2.
; It opens and closes the channels it creates.

(in-package "ACL2")

(set-state-ok t)

(defun copy-file1 (channel1 channel2 state)
  (declare (xargs :mode :program))
  (mv-let (byte state)
    (read-byte$ channel1 state)
    (cond
     ((null byte) state)
     (t (let ((state (write-byte$ byte channel2 state)))
          (copy-file1 channel1 channel2 state))))))

(defun copy-file (file1 file2 state)
  (declare (xargs :mode :program))
  (mv-let (channel1 state)
    (open-input-channel file1 :byte state)
    (mv-let (channel2 state)
      (open-output-channel file2 :byte state)
      (let* ((state (copy-file1 channel1 channel2 state))
             (state (close-output-channel channel2 state))
             (state (close-input-channel channel1 state)))
        state))))





