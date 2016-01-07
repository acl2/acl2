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

(defun dirname-fn (path state)
  (b* (((unless (live-state-p state))
        (error "DIRNAME can only be called on a live state.")
        (mv "ERROR" nil state))
       ((unless (stringp path))
        (error "DIRNAME called on a non-stringp dir?")
        (mv "ERROR" nil state))

       ((when (equal path ""))
        ;; Special case for the empty string, to match unix dirname command better.
        (mv nil "." state)))

    (handler-case
      ;; This is a nightmare.
      ;;
      ;; I thought I could just use:
      ;;    (cl-fad:pathname-parent-directory pathname)
      ;; But that doesn't work.
      ;;
      ;; It works fine when I use a path like: /home/users/jared/  (note the trailing slash).
      ;; E.g.,:
      ;;   (cl-fad:pathname-parent-directory (pathname "/home/users/jared/"))   --> #P"/home/users/"
      ;;
      ;; But not when I have a path like: /home/users/jared (note no trailing slash).
      ;; Here it produces a completely nonsense answer:
      ;;   (cl-fad:pathname-parent-directory (pathname "/home/users/jared")) --> #P"/home/jared"
      ;;
      ;; A fix seems to be to use pathname-as-directory to normalize the path.
      ;; In particular:
      ;;
      ;;   (cl-fad:pathname-as-directory (pathname "/home/users/jared"))  --> #P"/home/users/jared/"
      ;;   (cl-fad:pathname-as-directory (pathname "/home/users/jared/")) --> #P"/home/users/jared/"
      ;;
      ;; So either way we get to the case where pathname-parent-directory will work.
      (mv nil

          ;; CL-FAD based implementation
          ;; (namestring (cl-fad:pathname-parent-directory
          ;;              (cl-fad:pathname-as-directory
          ;;               (pathname path))))

          ;; It seems that UIOP is now preferred over CL-FAD.  The same kind of
          ;; discussion seems to apply, although pathname-as-directory is now
          ;; renamed.

          ;; It seems like a good idea to use the UIOP native-namestring
          ;; functions for a better chance at compatibility across Lisps,
          ;; rather than namestring and pathname.
          (uiop:native-namestring
           (uiop:pathname-parent-directory-pathname
            (uiop:ensure-directory-pathname
             (uiop:parse-native-namestring path))))

          state)
      (error (condition)
             (let ((condition-str (format nil "~a" condition)))
               (mv (msg "~s0: error getting dirname of ~s1: ~s2."
                        'dirname path condition-str)))))))


(defun basename-fn (path state)
  (b* (((unless (live-state-p state))
        (error "BASENAME can only be called on a live state.")
        (mv "ERROR" nil state))
       ((unless (stringp path))
        (error "BASENAME called on a non-stringp dir?")
        (mv "ERROR" nil state)))
    (handler-case
      (b* (((when (equal path ""))
            ;; Avoid tricky case for better compatibility with Unix basename command.
            (mv nil "" state))

;; [BOZO] may not be necessary if UIOP/CMUCL path issues get fixed.
           ((when (equal path "."))
            ;; Avoid case where the below doesn't work correctly on CMUCL.
            ;; This is very unsatisfying.
            (mv nil "." state))

           (pathname (uiop:parse-native-namestring path))
           ((unless (uiop:directory-pathname-p pathname))
            ;; Easy case, can just get the file name.
            (mv nil (file-namestring pathname) state))

           ;; Hard case.  We've been given something like /home/jared/, so
           ;; pathname has no file part, only a directory part.  In this case
           ;; the unix basename tool will return "jared".  I don't see any
           ;; sensible way to extract just the last directory name.  So after
           ;; much frustrating hacking trying to find a suitable combination of
           ;; UIOP/CL-FAD functions, I said "screw this" and just wrote
           ;; something horrible.  Hopefully some day someone can rewrite this
           ;; to be more sensible.
           (dirpart (pathname-directory pathname))
           ;; (- (cl-user::format t "dirpart is ~s~%" dirpart))

           ;; This seems to return something like
           ;;   - (:absolute "home" "jared")     for "/home/jared/"
           ;;   - (:relative "." "foo")          for "./foo/"
           ;;   - (:absolute)                    for "/"
           ;;   - NIL                            for ""
           ;; I ruled out "" above.
           ((unless (and (consp dirpart)
                         (or (eq (car dirpart) :relative)
                             (eq (car dirpart) :absolute))))
            (mv (msg "~s0: unsupported result from pathname-directory: ~x1. (path ~s2)"
                     'basename dirpart path)
                "" state))

           ((cons type pieces) dirpart)

           (pieces
            ;; Hack for SBCL, where a path like "////" produces (:absolute "" "" "")
            (remove-equal "" pieces))

           ((when (and (eq type :absolute)
                       (not pieces)))
            ;; BOZO probably not sensible on Windows
            (mv nil "/" state))

;; [BOZO] may not be necessary if UIOP/CMUCL path issues get fixed.
           #+cmu
           ((when (and (eq type :relative)
                       (not pieces)))
            ;; CMUCL seems to end up with this for paths like "./"
            (mv nil "." state))

           ((unless (consp pieces))
            (mv (msg "~s0: unsupported result from pathname-directory: ~x1. (path ~s2)"
                     'basename dirpart path)
                "" state))

           (last-piece (car (last pieces)))
           ((when
                #-cmu (eq last-piece :up)
                #+cmu (eq last-piece :back))
            (mv nil ".." state))
           ((when (stringp last-piece))
            (mv nil last-piece state)))
        (mv (msg "~s0: unrecgonized last piece ~s1 in pathname-directory dirpart: ~x2. (path ~s3)"
                 'basename last-piece dirpart path)
            "" state))

      (error (condition)
             (let ((condition-str (format nil "~a" condition)))
               (mv (msg "~s0: error getting basename of ~s1: ~s2."
                        'basename path condition-str)))))))
