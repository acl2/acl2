; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;   Kookamara LLC
;   11410 Windermere Meadows, Austin TX, 78759, USA.
;   http://www.kookamara.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "SIDEKICK")

(defvar *server* nil)

(defun start-fn (port)
  (when *server*
    (stop))
  (let* ((port (or port
                   (b* ((state acl2::*the-live-state*)
                        ((mv ? port state) (getenv$ "SIDEKICK_PORT" state)))
                     (or (str::strval port)
                         9000))))
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
    (format t ";           Sidekick started, see http://localhost:~D/~%" port)
    (format t ";~%")
    (format t "; ----------------------------------------------------------------~%~%")
    (add-handlers)
    (setq *server* server))
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


; For some reason, reading using "read-string" sometimes initializes a hons
; space.  But we want this to be fast.  So, make the hons space we create
; small, and ensure that acl2-par is set so that we can set the default-hs to
; nil.

#-acl2-par
(error "The ACL2 Sidekick requires that ACL2 be compiled with ACL2(p) support
        enabled.")

(setq acl2::*hl-hspace-str-ht-default-size*      100)
(setq acl2::*hl-ctables-nil-ht-default-size*     100)
(setq acl2::*hl-ctables-cdr-ht-default-size*     100)
(setq acl2::*hl-ctables-cdr-ht-eql-default-size* 100)
(setq acl2::*hl-hspace-addr-ht-default-size*     100)
(setq acl2::*hl-hspace-sbits-default-size*       100)
(setq acl2::*hl-hspace-other-ht-default-size*    100)
(setq acl2::*hl-hspace-fal-ht-default-size*      100)
(setq acl2::*hl-hspace-persist-ht-default-size*  100)

(defun add-handlers ()
  (hunchentoot:define-easy-handler (say-yo :uri "/yo") (name)
    (setf (hunchentoot:content-type*) "application/json")
    (bridge::json-encode
     (list 'foo :name name)))

  (hunchentoot:define-easy-handler (pbt-handler :uri "/pbt") ()
     (setf (hunchentoot:content-type*) "application/json")
     (b* ((state acl2::*the-live-state*)
          (world (w state))
          ((when (and *pbt-cached-result* (eq world *pbt-cached-world*)))
           *pbt-cached-result*)
          ((mv er val ?state) (acl2::json-pbt 0))
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
          ((mv er val ?state) (acl2::json-pbt :x)))
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
          ((mv er val ?state) (acl2::json-pcb! num fullp)))
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
          ((mv er val ?state) (acl2::json-pc num)))
       (bridge::json-encode
        (list (cons :error er)
              (cons :val val)))))

  (hunchentoot:define-easy-handler (disassemble-handler :uri "/disassemble") (name)
     (setf (hunchentoot:content-type*) "application/json")
     (b* ((state acl2::*the-live-state*)
          (acl2::*default-hs* nil)
          ((mv errmsg objs state) (acl2::read-string name))
          ((when errmsg)
           (bridge::json-encode
            (list (cons :error (format nil "Error in disassemble: parsing failed: ~a: ~a~%"
                                       name errmsg))
                  (cons :val ""))))
          ((unless (and (equal (len objs) 1)
                        (symbolp (car objs))))
           (bridge::json-encode
            (list (cons :error (format nil "Error in disassemble: not a symbol: ~a~%" name))
                  (cons :val ""))))
          ((mv disassembly ?state)
           (disassemble-to-string (car objs) state)))
       (bridge::json-encode
        (list (cons :error nil)
              (cons :val disassembly)))))

  (hunchentoot:define-easy-handler (props-handler :uri "/props") (name)
     (setf (hunchentoot:content-type*) "application/json")
     (b* ((state acl2::*the-live-state*)
          (acl2::*default-hs* nil)
          ((mv errmsg objs state) (acl2::read-string name))
          ((when errmsg)
           (bridge::json-encode
            (list (cons :error (format nil "Error in props: parsing failed: ~a: ~a~%"
                                       name errmsg))
                  (cons :val ""))))
          ((unless (and (equal (len objs) 1)
                        (symbolp (car objs))))
           (bridge::json-encode
            (list (cons :error (format nil "Error in props: not a symbol: ~a~%" name))
                  (cons :val ""))))
          ((mv props ?state)
           (props-jalist (car objs) state)))
       (bridge::json-encode
        (list (cons :error nil)
              (cons :val props)))))

  (hunchentoot:define-easy-handler (origin-handler :uri "/origin") (name)
     (setf (hunchentoot:content-type*) "application/json")
     (b* ((state acl2::*the-live-state*)
          (acl2::*default-hs* nil)
          ((mv errmsg objs state) (acl2::read-string name))
          ((when errmsg)
           (bridge::json-encode
            (list (cons :error (format nil "Error in origin: parsing failed: ~a: ~a~%"
                                       name errmsg))
                  (cons :val ""))))
          ((unless (and (equal (len objs) 1)
                        (symbolp (car objs))))
           (bridge::json-encode
            (list (cons :error (format nil "Error in origin: not a symbol: ~a~%" name))
                  (cons :val ""))))
          ((mv er val ?state)
           (acl2::origin-fn (car objs) state)))
       (bridge::json-encode
        (list (cons :error nil)
              (cons :val val)))))

  (hunchentoot:define-easy-handler (xdoc-handler :uri "/xdoc") (name)
     (setf (hunchentoot:content-type*) "application/json")
     (b* ((state acl2::*the-live-state*)
          (acl2::*default-hs* nil)
          ((mv errmsg objs state) (acl2::read-string name))
          ((when errmsg)
           (bridge::json-encode
            (list (cons :error (format nil "Error in origin: parsing failed: ~a: ~a~%"
                                       name errmsg))
                  (cons :val ""))))
          ((unless (and (equal (len objs) 1)
                        (symbolp (car objs))))
           (bridge::json-encode
            (list (cons :error (format nil "Error in origin: not a symbol: ~a~%" name))
                  (cons :val ""))))
          (name (car objs))
          ((mv out ?state) (json-xdoc-topic name state)))
       out))

  (hunchentoot:define-easy-handler (webcommand-handler :uri "/webcommands") ()
     (setf (hunchentoot:content-type*) "application/json")
     (b* ((commands (get-webcommands-stack)))
       (bridge::json-encode
        (list (cons :commands commands))))))




