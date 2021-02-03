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

(in-package "ACL2")
(include-book "../ls")
(include-book "../catpath")
(include-book "std/util/defconsts" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)

(defconsts (*files* state)
  (oslib::ls! "."))

(assert! (member-equal ".fileforls" *files*))
(assert! (member-equal "ls.lisp" *files*))
(assert! (member-equal "top.lisp" *files*))
(assert! (not (member-equal "." *files*)))
(assert! (not (member-equal ".." *files*)))

;; (defconsts (*acl2-all* state)
;;   (b* ((acl2-src-dir (f-get-global 'acl2::acl2-sources-dir state)))
;;     (oslib::ls! acl2-src-dir)))

;; (assert! (member-equal "axioms.lisp" *acl2-all*))  ;; Regular file with extension
;; (assert! (member-equal "Makefile" *acl2-all*))     ;; Regular file without extension
;; (assert! (member-equal "emacs" *acl2-all*))        ;; Directory


(defconsts (*files2* state)
  (oslib::ls! "../"))

(defconsts (*files3* state)
  (b* ((acl2-src-dir (f-get-global 'acl2::system-books-dir state))
       (oslib-dir    (oslib::catpath acl2-src-dir "oslib")))
    (oslib::ls! oslib-dir)))

(defconsts (*files4* state)
  (b* ((acl2-src-dir (f-get-global 'acl2::system-books-dir state))
       (oslib-dir    (oslib::catpath acl2-src-dir "oslib/../oslib")))
    (oslib::ls! oslib-dir)))

(assert! (member-equal "ls-logic.lisp" *files2*))
(assert! (member-equal "ls-logic.lisp" *files3*))
(assert! (member-equal "ls-logic.lisp" *files4*))

(defconsts (*acl2reg* state)
  (b* ((acl2-src-dir (f-get-global 'acl2::acl2-sources-dir state)))
    (oslib::ls-files! acl2-src-dir)))

(assert! (member-equal "axioms.lisp" *acl2reg*))
;; (assert! (subsetp-equal *acl2reg* *acl2-all*))

;; (defconsts (*acl2dirs* state)
;;   (b* ((acl2-src-dir (f-get-global 'acl2::acl2-sources-dir state)))
;;     (oslib::ls-subdirs! acl2-src-dir)))

;; (assert! (member-equal "emacs" *acl2dirs*))
;; (assert! (subsetp-equal *acl2dirs* *acl2-all*))

;; sswords: this test fails whenever there is somethink like a broken symlink
;; in the acl2 directory -- and emacs sometimes leaves behind broken symlinks
;; named .#foobar, I think to record who is editing the file. Removing the test
;; for now since it doesn't seem important.
;; (assert! (or (subsetp-equal *acl2-all* (append *acl2dirs* *acl2reg*))
;;              (cw "Oops, somehow acl2-all has files that aren't dirs or regular? ~x0~%"
;;                  (set-difference-equal *acl2-all*
;;                                        (append *acl2dirs* *acl2reg*)))))

;; (assert! (or (not (intersection-equal *acl2dirs* *acl2reg*))
;;              (cw "Oops, intersecting files and dirs?  ~x0~%"
;;                  (intersection-equal *acl2dirs* *acl2reg*))))

(defconsts (*err* *val* state)
  ;; There was once a bug with ls-fn's raw lisp definition where it was
  ;; returning (mv (msg ...)) instead of (mv (msg ...) nil state) in an error
  ;; case.  This led to a horrible error message about latch-stobjs1.  At any
  ;; rate, it's a good idea to test that trying to list non-existent dirs
  ;; really do cause errors.
  (oslib::ls "/this-directory-should-not-exist/or-else/this-test/will-fail"))

(assert! *err*)
(assert! (not *val*))


;; I later found that there were problems following ".." paths in certain
;; directories.  See lstest-dir.sh for the setup and comments about it.

(defttag sys-call)

(make-event
 (b* ((- (cw "Preparing lstest-dir.~%"))
      (cbd    (cbd))
      (script (oslib::catpath cbd "make-lstest.sh"))
      ((mv err val state) (sys-call+ script nil state))
      (- (cw "~S0" val))
      (- (or (not err)
             (er hard? 'make-lstest.sh
                 "Error running make-lstest.sh: err ~x0 val ~x1"
                 err val))))
   (value '(value-triple :invisible))))

(defmacro ensure-has (dir file)
  `(make-event
    (b* ((dir ',dir)
         (file ',file)
         (- (cw "Checking ~s0 for ~s1: " dir file))
         ((mv files state) (oslib::ls-files! dir))
         ((when (member-equal file files))
          (cw "found.~%")
          (value '(value-triple :success))))
      (er soft 'ensure-has "File ~s0 not found in ~s1: found files are ~x2"
          file dir files))))

(ensure-has "lstest-dir" "file1.txt")
(ensure-has "lstest-dir/subdir1" "file2.txt")
(ensure-has "lstest-dir/subdir1/xxxdir" "xxx.txt")
(ensure-has "lstest-dir/subdir1/subdir2" "file3.txt")
(ensure-has "lstest-dir/subdir1/subdir2/yyydir" "yyy.txt")

;; this doesn't work yet
;; subdir3 is a symlink to subdir1/subdir2, so when we do subdir3/.., we
;; should end up in subdir1(!)
;; (ensure-has "lstest-dir/subdir3/.." "file2.txt")
