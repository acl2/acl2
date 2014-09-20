; OSLIB -- Operating System Utilities
; Copyright (C) 2013-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "OSLIB")
(include-book "../copy")
(include-book "../ls")
(include-book "../rmtree")
(include-book "../mkdir")
(defttag :sys-call)

(define is-copy-p ((a stringp)
                   (b stringp)
                   &key
                   (state 'state))
  (b* (((mv erp ?val state) (sys-call+ "diff" (list a b) state))
       ((unless erp)
        ;; Diff returned 0, so that means they're the same
        (mv t state)))
    (mv nil state)))

(define is-copy-p! ((a stringp)
                    (b stringp)
                    &key
                    (state 'state))
  (b* (((mv copy-p state) (is-copy-p a b))
       ((unless copy-p)
        (raise "~s0 is not a copy of ~s1." a b)
        state))
    state))

;; (defmacro assert-is-copy (a b)
;;   `(make-event
;;     (b* ((state (is-copy-p! ,a ,b)))
;;       (value '(value-triple :success)))))

(define copy-file! ((from stringp)
                    (to stringp)
                    &key
                    ((overwrite booleanp) 'nil)
                    (state 'state))
  (b* (((mv err state) (copy-file from to :overwrite overwrite))
       ((when err)
        (cw "ERR is ~x0.~%" err)
        (raise "Copy file failed: ~@0" err)
        state))
    state))

(make-event
 (b* ((- (cw "Test: primitive copy file to non-existent file.~%"))
      (state (rmtree! "./copy-tests-tmp"))
      (state (mkdir! "./copy-tests-tmp"))
      (state (copy-file! "copy.lisp" "copy-tests-tmp/copy.txt"))
      (state (is-copy-p! "copy.lisp" "copy-tests-tmp/copy.txt")))
   (value '(value-triple :success))))

(make-event
 (b* ((- (cw "Test: primitive copy-file trying to overwrite directory.~%"))
      (state (rmtree! "./copy-tests-tmp"))
      (state (mkdir! "./copy-tests-tmp"))
      ((mv err state) (copy-file "copy.lisp" "copy-tests-tmp"))
      ((unless err)
       (er soft 'copy-file "Expected copy-file to fail to copy to directory.")))
   (cw "Successfully got error: ~@0" err)
   (value '(value-triple :success))))

(make-event
 (b* ((- (cw "Test: primitive copy-file trying to copy a directory.~%"))
      (state (rmtree! "./copy-tests-tmp"))
      (state (mkdir! "./copy-tests-tmp"))
      ((mv err state) (copy-file "./copy-tests-tmp" "./copy-tests-tmp2"))
      ((unless err)
       (er soft 'copy-file "Expected copy-file to fail to copy directory.")))
   (cw "Successfully got error: ~@0" err)
   (value '(value-triple :success))))

#+Linux
(make-event
 (b* ((- (cw "Test: primitive copy-file to /root where we should have no permission.~%"))
      ((mv err state) (copy-file "./copy.lisp" "/root/foo"))
      ((unless err)
       (er soft 'copy-file "Expected copy-file to fail to copy to /root.")))
   (cw "Successfully got error: ~@0" err)
   (value '(value-triple :success))))


(make-event
 (b* ((- (cw "Test: copy regular file to new file.~%"))
      (state (rmtree! "copy-tests-tmp"))
      (state (copy! "copy.lisp" "copy-tests-tmp"))
      (state (is-copy-p! "copy.lisp" "copy-tests-tmp"))
      (state (rmtree! "copy-tests-tmp")))
   (value '(value-triple :success))))

(make-event
 (b* ((- (cw "Test: copy regular file to overwrite file.~%"))
      (state (rmtree! "copy-tests-tmp"))
      (state (copy! "copy.lisp" "copy-tests-tmp"))
      (state (is-copy-p! "copy.lisp" "copy-tests-tmp"))
      (state (copy! "top.lisp" "copy-tests-tmp" :overwrite t))
      (state (is-copy-p! "top.lisp" "copy-tests-tmp"))
      (state (rmtree! "copy-tests-tmp")))
   (value '(value-triple :success))))

(make-event
 (b* ((- (cw "Test: copy should fail to overwrite file.~%"))
      (state (rmtree! "copy-tests-tmp"))
      (state (copy! "copy.lisp" "copy-tests-tmp"))
      (state (is-copy-p! "copy.lisp" "copy-tests-tmp"))
      ((mv err state) (copy "top.lisp" "copy-tests-tmp"))
      ((unless err)
       (er soft 'copy "Expected copy should fail."))
      (- (cw "Successfully got expected error: ~@0." err))
      (state (rmtree! "copy-tests-tmp")))
   (value '(value-triple :success))))

(make-event
 (b* ((- (cw "Test: copy regular file to into empty dir.~%"))
      (state (rmtree! "copy-tests-tmp"))
      (state (mkdir! "copy-tests-tmp"))
      (state (copy! "copy.lisp" "copy-tests-tmp"))
      (state (is-copy-p! "copy.lisp" "copy-tests-tmp/copy.lisp"))
      (state (rmtree! "./copy-tests-tmp")))
   (value '(value-triple :success))))

(make-event
 (b* ((- (cw "Test: copy regular file to into empty dir, explicit name.~%"))
      (state (rmtree! "copy-tests-tmp"))
      (state (mkdir! "copy-tests-tmp"))
      (state (copy! "copy.lisp" "copy-tests-tmp/mycopy.txt"))
      (state (is-copy-p! "copy.lisp" "copy-tests-tmp/mycopy.txt"))
      (state (rmtree! "./copy-tests-tmp")))
   (value '(value-triple :success))))

(make-event
 (b* ((- (cw "Test: fail to overwrite, tricky case.~%"))
      (state (rmtree! "copy-tests-tmp"))
      (state (mkdir! "copy-tests-tmp"))
      (state (copy! "copy.lisp" "copy-tests-tmp"))
      (state (is-copy-p! "copy.lisp" "copy-tests-tmp/copy.lisp"))
      ((mv err state) (copy "copy.lisp" "copy-tests-tmp"))
      ((unless err) (er soft 'copy "Failed to prevent copy."))
      (- (cw "Successfully got error: ~@0.~%" err))
      (state (rmtree! "./copy-tests-tmp")))
   (value '(value-triple :success))))

(make-event
 (b* ((- (cw "Test: copy basic directory recursively.~%"))
      (state (rmtree! "./copy-tests-tmp"))
      (state (mkdir! "./copy-tests-tmp"))
      (state (mkdir! "./copy-tests-tmp/tmp1"))
      (state (mkdir! "./copy-tests-tmp/tmp2"))
      (state (copy! "copy.lisp" "copy-tests-tmp"))
      (state (copy! "copy.lisp" "copy-tests-tmp/copyx.txt"))
      (state (copy! "copy.lisp" "copy-tests-tmp/tmp1/copy1.txt"))
      (state (copy! "copy.lisp" "copy-tests-tmp/tmp1/copy2.txt"))
      (state (copy! "copy.lisp" "copy-tests-tmp/tmp2/copya.txt"))
      (state (copy! "copy.lisp" "copy-tests-tmp/tmp2/copyb.txt"))
      (state (rmtree! "./copy-tests-tmp2"))
      (state (copy! "copy-tests-tmp" "copy-tests-tmp2" :recursive t))
      (state (is-copy-p! "copy.lisp" "copy-tests-tmp2/copy.lisp"))
      (state (is-copy-p! "copy.lisp" "copy-tests-tmp2/copyx.txt"))
      (state (is-copy-p! "copy.lisp" "copy-tests-tmp2/tmp1/copy1.txt"))
      (state (is-copy-p! "copy.lisp" "copy-tests-tmp2/tmp1/copy2.txt"))
      (state (is-copy-p! "copy.lisp" "copy-tests-tmp2/tmp2/copya.txt"))
      (state (is-copy-p! "copy.lisp" "copy-tests-tmp2/tmp2/copyb.txt"))
      (state (rmtree! "./copy-tests-tmp"))
      (state (rmtree! "./copy-tests-tmp2")))
   (value '(value-triple :success))))
