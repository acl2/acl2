; Copyright (C) 2022 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>


(er-let* ((name (getenv$ "ACL2_IMAGE_NAME" state)))
  (ld (concatenate 'string name ".lsp")))

(make-event
 (er-let* ((name (getenv$ "ACL2_IMAGE_NAME" state)))
   (value `(local (defconst *acl2-image-name* ,name)))))


(value :q)

(er-let* ((dir1 (getenv$ "ACL2_IMAGES" acl2::*the-live-state*))
          (dir2 (getenv$ "CERT_PL_BIN_DIR" acl2::*the-live-state*)))
  (let* ((dir (or dir1 dir2))
         (file (our-merge-pathnames dir *acl2-image-name*)))
    (prog2$ (cw "file to write: ~s0~%" file)
            (save-exec file *acl2-image-message*))))

