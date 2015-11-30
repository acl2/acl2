; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
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

(in-package "SIDEKICK")
(include-book "io")
(include-book "xdoc/save" :dir :system)
(set-state-ok t)
(program)

(define props-jalist-aux (alist (config str::printconfig-p))
  (b* (((when (atom alist))
        nil)
       ((cons key val) (car alist)))
    (cons (cons key (str::pretty val :config config))
          (props-jalist-aux (cdr alist) config))))

(define props-jalist (name state)
  (b* (((unless (symbolp name))
        nil)
       (world  (w state))
       (alist  (getprops name 'acl2::current-acl2-world world))
       (pkg    (current-package state))
       (config (str::make-printconfig :home-package (pkg-witness pkg)
                                      :print-lowercase t
                                      :hard-right-margin 60
                                      ))
       (pretty-printed-alist (props-jalist-aux alist config)))
    pretty-printed-alist))

(define sk-get-props ((name stringp) state)
  :returns (mv json-props state)
  (b* (((mv errmsg objs state) (acl2::read-string name))
       ((when errmsg)
        (mv (sk-json-error "Error in props: parsing failed: ~a: ~a" name errmsg)
            state))
       ((unless (and (equal (len objs) 1)
                     (symbolp (car objs))))
        (mv (sk-json-error "Error in props: not a symbol: ~a" name)
            state))
       (props (props-jalist (car objs) state)))
    (mv (bridge::json-encode
         (list (cons :error nil)
               (cons :val props)))
        state)))

(define sk-get-origin ((name stringp) state)
  :returns (mv json-props state)
  (b* (((mv errmsg objs state) (acl2::read-string name))
       ((when errmsg)
        (mv (sk-json-error "Error in origin: parsing failed: ~a: ~a~%" name errmsg)
            state))
       ((unless (and (equal (len objs) 1)
                     (symbolp (car objs))))
        (mv (sk-json-error "Error in origin: not a symbol: ~a~%" name)
            state))
       ((mv ?er val ?state)
        (acl2::origin-fn (car objs) state)))
    (mv (bridge::json-encode (list (cons :error nil)
                                   (cons :val val)))
        state)))

(defun json-xdoc-topic (name state)
  (b* (((mv ? topics state)  (xdoc::all-xdoc-topics state))
       (topics-fal           (xdoc::topics-fal topics))
       (topic                (cdr (hons-get name topics-fal)))
       ((unless topic)
        (mv (sk-json-error "No xdoc for topic ~a~%" name)
            state))
       ((mv short-str state) (xdoc::short-xml-for-topic topic topics-fal state))
       ((mv long-str  state) (xdoc::long-xml-for-topic  topic topics-fal state)))
    (mv (bridge::json-encode
         (list (cons :error nil)
               (cons :short short-str)
               (cons :long long-str)))
        state)))

(define sk-get-xdoc ((name stringp) state)
  :returns (mv json-props state)
  (b* (((mv errmsg objs state) (acl2::read-string name))
       ((when errmsg)
        (mv (sk-json-error "Error in origin: parsing failed: ~a: ~a~%" name errmsg)
            state))
       ((unless (and (equal (len objs) 1)
                     (symbolp (car objs))))
        (mv (sk-json-error "Error in origin: not a symbol: ~a~%" name)
            state))
       ((mv out state) (json-xdoc-topic (car objs) state)))
    (mv out state)))
