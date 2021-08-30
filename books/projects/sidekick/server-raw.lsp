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

(acl2::mf-multiprocessing t)

(defvar *server* nil)

(defun maybe-launch-browser (host port)
  (b* ((state acl2::*the-live-state*)
       ((mv ? browser state) (getenv$ "SIDEKICK_BROWSER" state))
       ((unless (and (stringp browser)
                     (not (equal browser ""))))
        nil))
    (acl2::tshell-ensure)
    (acl2::tshell-run-background
     (str::cat browser " http://" host ":" (str::natstr port) "/"))))

(defun start-fn (port)
  (when *server*
    (stop))
  (let* ((port (or port
                   (b* ((state acl2::*the-live-state*)
                        ((mv ? port state) (getenv$ "SIDEKICK_PORT" state))
                        (port-num (and port (str::strval port)))
                        ((when port-num)
                         port-num)
                        ;; Special hack for Centaur: fall back to FVQ_PORT if
                        ;; it is defined.
                        ((mv ? port state) (getenv$ "FVQ_PORT" state))
                        (port-num (and port (str::strval port)))
                        ((when port-num)
                         port-num))
                     ;; Else, just use the default port
                     9000)))

         ;; For complicated cluster setups, you might want to fudge the host in
         ;; the usage message and in maybe-launch-browser.
         (host (b* (((mv ? host state) (getenv$ "SIDEKICK_HOST" state))
                    ((when (and (stringp host)
                                (not (equal host ""))))
                     host))
                 "localhost"))
         (root
          ;; Note: apparently this has to include the trailing slash!
          (str::cat *sidekick-dir* "/public/"))
         (server (make-instance 'hunchentoot:easy-acceptor
                                :port port
                                :document-root root)))
    (setf (hunchentoot:acceptor-access-log-destination server)
          (str::cat *sidekick-dir* "/access.out"))
    (hunchentoot:start server)
    (format t "; ----------------------------------------------------------------~%")
    (format t ";~%")
    (format t ";           Sidekick started, see http://~a:~D/~%" host port)
    (format t ";~%")
    (format t "; ----------------------------------------------------------------~%~%")
    (add-handlers)
    (setq *server* server)
    (maybe-launch-browser host port))
  nil)

(defun stop ()
  (when *server*
    (hunchentoot:stop *server*)
    (setq *server* nil))
  nil)


; We go to some trouble to cache PBT results so that the client can poll it
; frequently.  We could do more to cache other results like PBT and PCB
; results, but this seems pretty workable so far.

(defvar *pbt-cached-world* nil)
(defvar *pbt-cached-result* nil)

; Optimizations so that when new threads create hons spaces, these spaces are
; small.
(setq acl2::*hl-hspace-str-ht-default-size*      100)
(setq acl2::*hl-ctables-nil-ht-default-size*     100)
(setq acl2::*hl-ctables-cdr-ht-default-size*     100)
(setq acl2::*hl-ctables-cdr-ht-eql-default-size* 100)
(setq acl2::*hl-hspace-addr-ht-default-size*     100)
(setq acl2::*hl-hspace-sbits-default-size*       100)
(setq acl2::*hl-hspace-other-ht-default-size*    100)
(setq acl2::*hl-hspace-fal-ht-default-size*      100)
(setq acl2::*hl-hspace-persist-ht-default-size*  100)

(defmacro with-sidekick-bindings (&rest forms)
  `(b* ((?state
         ;; Bind state since we often need that.
         acl2::*the-live-state*)
        (acl2::*default-hs*
         ;; Give this thread its own hons space.  Hopefully it won't use it
         ;; for anything.
         nil)
        (acl2::*read-string-should-check-bad-lisp-object*
         ;; Turn this off because otherwise we run into hash table ownership
         ;; problems, because bad-lisp-objectp is memoized and memoization
         ;; isn't thread-safe.
         nil))
     . ,forms))

(defun add-handlers ()

  (hunchentoot:define-easy-handler (pbt-handler :uri "/pbt") ()
     (setf (hunchentoot:content-type*) "application/json")
     (b* ((state acl2::*the-live-state*)
          (world (w state))
          ((when (and *pbt-cached-result* (eq world *pbt-cached-world*)))
           *pbt-cached-result*)
          ((mv er val ?state) (json-pbt 0))
          (ans (bridge::json-encode
                (list (cons :error er)
                      (cons :val val)))))
       (setq *pbt-cached-world* world)
       (setq *pbt-cached-result* ans)
       (bridge::json-encode
        (list (cons :error er)
              (cons :val val)
              (cons :new t)))))

  (hunchentoot:define-easy-handler (pbtx-handler :uri "/pbtx") ()
     (setf (hunchentoot:content-type*) "application/json")
     (b* ((state acl2::*the-live-state*)
          (world (w state))
          ((mv er val ?state) (json-pbt :x)))
       (bridge::json-encode
        (list (cons :error er)
              (cons :val val)))))

  (hunchentoot:define-easy-handler (pcb-handler :uri "/pcb") (num full)
     (setf (hunchentoot:content-type*) "application/json")
     (b* ((num (or (str::strval num)
                   (and (equal num ":X") :x)
                   (and (equal num ":x") :x)
                   0))
          (state acl2::*the-live-state*)
          (fullp (equal full "1"))
          ((mv er val ?state) (json-pcb! num fullp)))
       (bridge::json-encode
        (list (cons :error er)
              (cons :val val)))))

  (hunchentoot:define-easy-handler (package-handler :uri "/package") ()
    (setf (hunchentoot:content-type*) "application/json")
    (b* ((state acl2::*the-live-state*)
         (pkg   (acl2::current-package state)))
      (bridge::json-encode
       (list (cons :package pkg)))))

  (hunchentoot:define-easy-handler (pc-handler :uri "/pc") (num)
     (setf (hunchentoot:content-type*) "application/json")
     (b* ((num (or (str::strval num)
                   (and (equal num ":X") :x)
                   (and (equal num ":x") :x)
                   0))
          (state acl2::*the-live-state*)
          ((mv er val ?state) (json-pc num)))
       (bridge::json-encode
        (list (cons :error er)
              (cons :val val)))))

  (hunchentoot:define-easy-handler (disassemble-handler :uri "/disassemble") (name)
     (setf (hunchentoot:content-type*) "application/json")
     (with-sidekick-bindings
       (b* (((mv ans state) (sk-get-disassembly name state)))
         ans)))

  (hunchentoot:define-easy-handler (lint-handler :uri "/lint") ()
     (setf (hunchentoot:content-type*) "application/json")
     (b* (((mv ans state) (json-lint state)))
       ans))

  (hunchentoot:define-easy-handler (props-handler :uri "/props") (name)
     (setf (hunchentoot:content-type*) "application/json")
     (with-sidekick-bindings
       (b* (((mv ans state) (sk-get-props name state)))
         ans)))

  (hunchentoot:define-easy-handler (origin-handler :uri "/origin") (name)
     (setf (hunchentoot:content-type*) "application/json")
     (with-sidekick-bindings
       (b* (((mv ans state) (sk-get-origin name state)))
         ans)))

  (hunchentoot:define-easy-handler (xdoc-handler :uri "/xdoc") (name)
     (setf (hunchentoot:content-type*) "application/json")
     (with-sidekick-bindings
       (b* (((mv ans state) (sk-get-xdoc name state)))
         ans)))

  (hunchentoot:define-easy-handler (webcommand-handler :uri "/webcommands") ()
     (setf (hunchentoot:content-type*) "application/json")
     (b* ((commands (get-webcommands-stack)))
       (bridge::json-encode
        (list (cons :commands commands)))))

  (hunchentoot:define-easy-handler (eventdata-handler :uri "/eventdata") (name)
     (setf (hunchentoot:content-type*) "application/json")
     (with-sidekick-bindings
       (b* (((mv ans state) (sk-get-eventdata name state)))
         ans)))

  (hunchentoot:define-easy-handler (ubt-handler :uri "/ubt" :default-request-type :post)
                                   ((n :parameter-type 'string))
    (setf (hunchentoot:content-type*) "application/json")
    (with-sidekick-bindings
      (b* (((mv ans state) (sk-undo-back-through n state)))
        ans)))

;; Proof explorer

  (hunchentoot:define-easy-handler (handle-explore-th :uri "/explore-th") ()
     (setf (hunchentoot:content-type*) "application/json")
     (with-sidekick-bindings
       (b* (((mv ans state) (sk-explore-th state)))
         ans)))

  (hunchentoot:define-easy-handler (handle-explore-commands :uri "/explore-commands") ()
     (setf (hunchentoot:content-type*) "application/json")
     (with-sidekick-bindings
       (b* (((mv ans state) (sk-explore-commands state)))
         ans)))

  (hunchentoot:define-easy-handler (explore-undo-handler :uri "/explore-undo" :default-request-type :post)
                                   ((n :parameter-type 'string))
    (setf (hunchentoot:content-type*) "application/json")
    (with-sidekick-bindings
      (b* (((mv ans state) (sk-explore-undo n state)))
        ans)))

  (hunchentoot:define-easy-handler (explore-contrapose-handler :uri "/explore-contrapose" :default-request-type :post)
                                   ((n :parameter-type 'string))
    (setf (hunchentoot:content-type*) "application/json")
    (with-sidekick-bindings
      (b* (((mv ans state) (sk-explore-contrapose n state)))
        ans)))

  (hunchentoot:define-easy-handler (explore-demote-handler :uri "/explore-demote" :default-request-type :post)
                                   ((n :parameter-type 'string))
    (setf (hunchentoot:content-type*) "application/json")
    (with-sidekick-bindings
      (b* (((mv ans state) (sk-explore-demote n state)))
        ans)))

  (hunchentoot:define-easy-handler (explore-drop-handler :uri "/explore-drop" :default-request-type :post)
                                   ((n :parameter-type 'string))
    (setf (hunchentoot:content-type*) "application/json")
    (with-sidekick-bindings
      (b* (((mv ans state) (sk-explore-drop n state)))
        ans)))

  (hunchentoot:define-easy-handler (explore-split-handler :uri "/explore-split" :default-request-type :post)
                                   ()
    (setf (hunchentoot:content-type*) "application/json")
    (with-sidekick-bindings
      (b* (((mv ans state) (sk-explore-split state)))
        ans)))

  (hunchentoot:define-easy-handler (explore-pro-handler :uri "/explore-pro" :default-request-type :post)
                                   ()
    (setf (hunchentoot:content-type*) "application/json")
    (with-sidekick-bindings
      (b* (((mv ans state) (sk-explore-pro state)))
        ans)))


  )
