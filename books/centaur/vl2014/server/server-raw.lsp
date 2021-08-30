; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")

(defmacro defxdoc-raw (&rest args)
  `(acl2::defxdoc-raw . ,args))

(defun set-vls-root (new-root)
  (setq *vls-root* new-root)
  (cw "; Note: reset *vls-root* to ~s0.~%" new-root))


; -----------------------------------------------------------------------------
;
;                           Thread-Safe Queues
;
; -----------------------------------------------------------------------------

(defxdoc-raw ts-queue
  :parents (server)
  :short "Primitive thread-safe, shared queue."

  :long "<p>Note that when using this queue, there is no way for the producer
to signal that he is done.  A consequence is that this queue structure should
only be used when consumers are continually looping and waiting for work to be
added to the queue.</p>

<p>This is appropriate, for instance, for the client handler threads that
always wait on the incoming connections queue for a new client to connect, and
for the loader thread that is always and forever waiting to be told to load new
models.</p>")

(defstruct ts-queue
  ;; SEM is signaled whenever new data is added to the queue by a producer.
  ;; Consumers wait for SEM to take the next available object.
  (sem  (bt-semaphore:make-semaphore))

  ;; LOCK must be acquired whenever a producer or consumer needs to modify DATA
  ;; to insert or extract a value.
  (lock (bt:make-lock "ts-queue lock"))

  ;; DATA contains the actual queue data.  We enqueue elements into the back of
  ;; DATA and dequeue from the front.
  (data nil))

(defxdoc-raw ts-enqueue
  :parents (ts-queue)
  :short "@('(ts-enqueue obj queue)') safely adds @('obj') to @('queue'),
signals the queue's semaphore to allow the object to be consumed by some
consumer, and finally returns @('obj').")

(defun ts-enqueue (obj queue)
  (declare (type ts-queue queue))
  (bt:with-lock-held ((ts-queue-lock queue))
                     (setf (ts-queue-data queue)
                           (append (ts-queue-data queue) (list obj))))
  (bt-semaphore:signal-semaphore (ts-queue-sem queue))
  obj)

(defxdoc-raw ts-dequeue
  :parents (ts-queue)
  :short "@('(ts-dequeue queue)') safely removes and returns the oldest object
from a queue.  If no objects are available, it blocks until an object is
added.")

(defun ts-dequeue (queue)
  (declare (type ts-queue queue))
  (bt-semaphore:wait-on-semaphore (ts-queue-sem queue))
  (bt:with-lock-held ((ts-queue-lock queue))
                     (let ((obj (car (ts-queue-data queue))))
                       (setf (ts-queue-data queue)
                             (cdr (ts-queue-data queue)))
                       obj)))

(defxdoc-raw ts-queue-len
  :parents (ts-queue)
  :short "@('(ts-queue-len queue)') returns the current length of the data list
for @('queue').  It can be used at any time by any thread and never blocks."

  :long "The return value of @('ts-queue-len') should only be treated as an
estimate.  This is because the length of the queue can change immediately after
@('ts-queue-len') returns (or even, right before it returns).")

(defun ts-queue-len (queue)
  (declare (type ts-queue queue))
  (bt:with-lock-held ((ts-queue-lock queue))
                     (length (ts-queue-data queue))))






; -----------------------------------------------------------------------------
;
;                           Translation Loading
;
; -----------------------------------------------------------------------------

(defxdoc-raw vls-transdb
  :parents (server)
  :short "Translations database for the VL Server."

  :long "<p>At a first approximation, the translation database acts like an
alist mapping translation names (see @(see vl-tname-p)) to their @(see
vls-data-p) contents.  However, the true story is somewhat more complex due to
the desire to keep translations loaded in a more persistent way.</p>

<p>VLS must be fast enough to respond to the web server in real time.  Even
using @(see serialize-read) with ordinary conses, loading a single translation
can take over a minute to load, so it is completely infeasible to imagine
loading translations on a per-connection basis.  Instead, we need some way to
keep translations pre-loaded.</p>

<p>This is a challenge due to the number and size of our translations.  At the
time of this writing, we are translating 12 versions of the chip every day, so
if we save translations for two weeks and don't translate on the weekend,
that's 120 models that VLS needs to provide access to.  It's easy to imagine
these numbers increasing.</p>

<p>We think it would take too long (and perhaps too much memory) to load
everything at once.  Instead, we will try to load translations only as the need
arises.  This might sometimes impose a 1-2 minute wait on a user who wants to
get started with a translation that isn't already loaded.  But, if we simply
make sure that all the translations in stable are pre-loaded, then this penalty
will probably only be encountered by users working with bleeding edge or older
translations.</p>

<p>It might be a good idea to come up with a way for translations to be
unloaded after they are no longer being used.  We haven't developed such a
mechanism yet, partially because our use of honsing means that the incremental
cost of having another module loaded is relatively low.</p>

<p>We hons translations as they are read.  An unfortunate consequence of this
is that our module loading is always done by a single loader thread, and hence
clients might in principle have to wait a long time for their translations to
be loaded if a long list of translations need to be loaded first.  Another
disadvantage of this approach, compared with ordinary conses, is that loading a
model takes perhaps two or three times as long, increasing the wait time for
the unfortunate user who wants to look at a model that is not yet loaded.</p>

<p>But we think these disadvantages are worth the memory savings since so much
structure sharing is found between translations.  At the time of this writing,
we found that to load ten translations took almost exactly twice as long with
hons (700 seconds instead of 350) but subsequently only required 10 GB of
memory instead of 16 GB to store (with 7 GB of this having been reserved for
the ADDR-HT).  As we imagine loading even more translations, this becomes a
pretty compelling advantage.</p>

<p>Note that all of this honsing is done with respect to the Hons Space in the
loader thread.  From the perspective of client threads, the modules being dealt
with are not normed.</p>")

(defstruct vls-transdb

  ;; SCANNED is the list of all translation names that we have detected in
  ;; /n/fv2/translations.  It is updated occasionally by vls-scanner-thread.
  ;; You must acquire SCANNED-LOCK when accessing or updating SCANNED.
  (scanned      nil)
  (scanned-lock (bt:make-lock "vls-transdb-scanned-lock"))

  ;; LOADED is an alist mapping tnames to their contents (vls-data-p objects).
  ;; It is updated by the vls-loader-thread, and perhaps in the future by some
  ;; kind of vls-unloader-thread.  You must acquire LOADED-LOCK when accessing
  ;; or updating this field.  Note also that the proper way to get a new
  ;; translation loaded is to add it to the LOAD-QUEUE via VLS-REQUEST-LOAD.
  (loaded      nil)
  (loaded-lock (bt:make-lock "vls-transdb-loaded-lock"))

  ;; LOAD-QUEUE is a TS-QUEUE that governs which translations are next to be
  ;; loaded by the loader thread.
  (load-queue  (make-ts-queue)))

(defparameter *vls-transdb* (make-vls-transdb))



(defun vls-scanner-thread (&optional noloop)

; Runs forever.  Lightweight.  Occasionally updates the list of SCANNED
; translation names to keep it in sync with the file system.  We do this in a
; separate thread because NFS can occasionally be slow and we don't want
; clients to have to wait for it when they connect.

  (let ((state acl2::*the-live-state*)
        (db    *vls-transdb*))
    (loop do
          (cl-user::format t "; vls-scanner-thread: scanning for new translations.~%")
          (handler-case
           (let ((new-scan (time$ (vl-scan-for-tnames state)
                                  :msg "; rescan: ~st sec, ~sa bytes~%")))
             (bt:with-lock-held ((vls-transdb-scanned-lock db))
                                (setf (vls-transdb-scanned db)
                                      new-scan))
             (sleep 600))
           (error (condition)
                  (cl-user::format t "Ignoring unexpected error in ~
                                      vls-scanner-thread: ~S~%"
                                   condition)))
          (when noloop
            (return-from vls-scanner-thread)))))

(defun rescan ()
  (vls-scanner-thread t))



(defun vls-scanned-translations (db)

; Safely access the list of translations that have been most recently returned
; by the scanner thread.

  (declare (type vls-transdb db))
  (bt:with-lock-held ((vls-transdb-scanned-lock db))
                     (vls-transdb-scanned db)))



(defun vls-load-translation (tname db)

; We attempt to load the translation specified by TNAME into DB.
;
; We assume that translations are never changed once they have been put into
; /n/fv2/translations, and so if they have been previously loaded and already
; exist in the LOADED alist, then they do not need to be re-loaded.
;
; It is critical that this function never be called except from the loader
; thread, because the use of honsing here should always be relative to the Hons
; Space of the loader thread.

  (declare (type vls-transdb db))
  (cl-user::format t "Running vls-loader-thread in ~a" (bt:thread-name (bt:current-thread)))
  (bt:with-lock-held
   ;; If it's already loaded, don't try to load it again.
   ((vls-transdb-loaded-lock db))
   (when (assoc-equal tname (vls-transdb-loaded db))
     (return-from vls-load-translation nil)))

; BOZO some better alternative to format messages here?  There probably really
; *isn't* a much better way to do this except perhaps to allow us to add an
; error string directly into the trandb-loaded alist, since this runs in a
; different thread than the load requests.

  (cl-user::format t "; vls-load-translation: loading base ~s, model ~s~%"
                   (vl-tname->base tname)
                   (vl-tname->model tname))

  (let* ((filename (vl-tname-xdat-file tname))
         (trans
          (acl2::with-suppression
            ;; BOZO with-suppression is necessary here for SBCL to avoid
            ;; package lock problems.  I've discussed this with Matt and it
            ;; sounds like he's probably going to make it so that
            ;; serialize-read automatically does with-suppression.  Once that
            ;; happens we should get rid of the with-suppression form here.
            (acl2::unsound-read filename :hons-mode :always :verbosep t))))
    (unless (cwtime (vl-translation-p trans))
      (cl-user::format t "; vls-load-translation: invalid translation data!~%")
      (return-from vls-load-translation nil))
    (let* ((data (vls-data-from-translation trans)))
      (bt:with-lock-held
       ((vls-transdb-loaded-lock db))
       (when (assoc-equal tname (vls-transdb-loaded db))
         (error "translation should not yet be loaded"))
       (setf (vls-transdb-loaded db)
             (acons tname data (vls-transdb-loaded db)))))))

(defun vls-loader-thread ()

; Runs forever.  Tries to load any translations that are added to the load
; queue.

  (let ((acl2::*default-hs*
         ;; Bigger sizes might be better for large models, but it might be nice
         ;; not to grow these beyond reason.
         ;; Bugfix 2014-12-05, do not call time$ here because it uses fmt, which
         ;; uses evisceration, which uses hons-assoc-equal and hence goes digging
         ;; through the hons space, which can cause hash table ownership problems.
         (acl2::hl-hspace-init :addr-ht-size 100000000
                               :sbits-size   100000000))
        (db *vls-transdb*))
    (cl-user::format t "; vls-loader-thread hons space allocated~%")
    (acl2::hons-summary)
    (acl2::hons-analyze-memory nil)
    ;; (format t "In vls-loader-thread, hons space is at ~s~%" (ccl::%address-of acl2::*default-hs*))
    (loop do
          (handler-case
           (let ((tname (ts-dequeue (vls-transdb-load-queue db))))
             (time$ (vls-load-translation tname db)))
           (error (condition)
                  (cl-user::format t "Ignoring unexpected error in ~
                                     vls-loader-thread: ~a~%"
                                   condition))))))


(let ((support-started nil))
  (defun maybe-start-support-threads ()
    (unless support-started
      (bt:make-thread 'vls-scanner-thread
                                    ;(list :name "vls-scanner-thread"
                                    ;      :stack-size  (* 8  (expt 2 20))  ;; 8 MB
                                    ;      :vstack-size (* 16 (expt 2 20))  ;; 16 MB
                                    ;      :tstack-size (* 8  (expt 2 20))  ;; 8 MB
                                    )
      (bt:make-thread 'vls-loader-thread
                                    ;; :stack-size  (* 8 (expt 2 20))   ;; 8 MB
                                    ;; :vstack-size (* 128 (expt 2 20)) ;; 128 MB
                                    ;; :tstack-size (* 8 (expt 2 20))   ;; 8 MB
                                    )
      (setq support-started t))))

(defun vls-loaded-translations (db)
  (alist-keys
   (bt:with-lock-held ((vls-transdb-loaded-lock db))
     (vls-transdb-loaded db))))

(defmacro with-vls-bindings (&rest forms)
  `(b* ((?state
         ;; Bind state since we often need that.
         acl2::*the-live-state*)

        ;; Hons space configuration.  Most threads probably don't need a hons
        ;; space at all.  For those that do, we'd like to make sure we create
        ;; hons spaces that are small so that creating threads isn't expensive.
        (acl2::*hl-hspace-addr-ht-default-size* 1000)
        (acl2::*hl-hspace-sbits-default-size*   1000)
        (acl2::*default-hs*                     nil)

        ;; I think we shouldn't need this anymore with thread-safe memoize?
        ;; (acl2::*read-string-should-check-bad-lisp-object*
        ;;  ;; Turn this off because otherwise we run into hash table ownership
        ;;  ;; problems, because bad-lisp-objectp is memoized and memoization
        ;;  ;; isn't thread-safe.
        ;;  nil)


        ;; Error Handling.  Make sure ACL2 hard errors get turned into Common
        ;; Lisp errors that we can catch properly.
        (acl2::*hard-error-is-error* t)
        (acl2::*hard-error-returns-nilp* nil))
     . ,forms))

(defun vls-quick-get-model (tname db)
  (bt:with-lock-held
    ;; If it's already loaded, don't try to load it again.
    ((vls-transdb-loaded-lock db))
    (let ((pair (assoc-equal tname (vls-transdb-loaded db))))
      (and pair
           (cdr pair)))))

(defun vls-start-model-load (tname db)
  (bt:with-lock-held
    ((vls-transdb-loaded-lock db))
    (ts-enqueue tname (vls-transdb-load-queue db))))

(defmacro define-constant (name value &optional doc)
  ;; See the SBCL manual, "Defining Constants"
  `(defconstant ,name (if (boundp ',name) (symbol-value ',name) ,value)
     ,@(when doc (list doc))))

(define-constant +vls-error-marker+
  ;; A unique cons for distinguishing trapped errors
  (cons :vls-error-marker nil))

(defun vls-error-handler (condition)
  (let ((msg (let ((*debug-io* (make-string-output-stream)))
               (cl-user::format *debug-io* "VL Server Error: ~a~%" condition)
               (cl-user::format *debug-io* "Backtrace:~%")
               (acl2::print-call-history)
               (get-output-stream-string *debug-io*))))
    (throw 'vls-error-handler (cons +vls-error-marker+ msg))))

(defmacro vls-try-catch (&key try catch)
  ;; Stupid awful mess of crap that emulates sane error handling.
  ;;
  ;; General Form:
  ;; (vls-try-catch :try <try-form>
  ;;                :catch <catch-form>)
  ;;
  ;; We attempt to evaluate and return the SINGLE value from <try-form>.
  ;;
  ;; If evaluation of <try-form> fails, we catch the error and turn it
  ;; into an error message, complete with a backtrace.  We then evaluate
  ;; <catch-form>.
  ;;
  ;; The <catch-form> can (and should) mention the variable ERRMSG.

  `(let ((errmsg ;; <-- goofy name but avoids inadvertent capture
          (catch 'vls-error-handler
            (handler-bind ((error #'vls-error-handler))
                          ,try))))
     ;; Result is now either: the result of running TRY (on success), or
     ;; the result of running VLS-ERROR-HANDLER (on failure).  We check
     ;; for this via the +vls-error-marker+.
     (if (and (consp errmsg)
              (eq (car errmsg) +vls-error-marker+))
         (let ((errmsg (cdr errmsg)))
           ,catch)
       errmsg)))


;; Small/simple demo to make sure it works.
(with-vls-bindings
  (let* ((oktest   (vls-try-catch
                    :try (+ 1 2)
                    :catch (list :whoops errmsg)))
         (failtest (vls-try-catch
                    :try (er hard? 'vls-try-catch-test "causing an error!")
                    :catch (list :whoops errmsg))))
    ;; Don't print these because they look scary
    ;; (cl-user::format t "OKTEST is ~a~%" oktest)
    ;; (cl-user::format t "FAILTEST is ~a~%" failtest)
    (assert (equal oktest 3))
    (assert (and (consp failtest)
                 (equal (first failtest) :whoops)
                 (stringp (second failtest))
                 (str::substrp "causing an error!" (second failtest))))))

(defun vls-add-automatic-command-handlers ()
  (let ((table (get-vls-commands (w acl2::*the-live-state*))))
    (loop for info in table collect
          (b* (((vls-commandinfo info))

               (autofn-name      (intern$ (cat "VLS-AUTO-HANDLER-FOR-" (symbol-name info.fn)) "VL2014"))
               (uri              (cat "/" (str::downcase-string (symbol-name info.fn))))
               (args-except-data (remove-equal 'data info.args))

               (params           (append
                                  '((base :parameter-type 'string)
                                    (model :parameter-type 'string))
                                  (loop for arg in args-except-data collect `(,arg :parameter-type 'string))))

               (content-type     (case info.type
                                   (:json "application/json")
                                   (:html "text/html")
                                   (otherwise (error "Invalid content type ~a" info.type))))

               (guts             `(with-vls-bindings
                                    (vls-try-catch
                                     :try (b* ((data (vls-quick-get-model (make-vl-tname :base base :model model) *vls-transdb*))
                                               ((unless data)
                                                ,(case info.type
                                                   (:json '(vls-fail "Error: invalid model (base ~s0, model ~s1)" base model))
                                                   (:html '(cat "Error: Invalid model (base " base ", model " model)))))
                                            (,info.fn . ,info.args))
                                     :catch
                                     ,(case info.type
                                        (:json '(vls-fail errmsg))
                                        (:html '(str::html-encode-string errmsg 8))))))

               (form `(hunchentoot:define-easy-handler (,autofn-name :uri ,uri)
                        ,params
                        (setf (hunchentoot:content-type*) ,content-type)
                        (time$ ,guts :msg ,(cat "; " uri ": ~st sec, ~sa bytes~%")))))
            (cl-user::format t "; Adding ~a~%" info.fn)
            (eval form)))))


(defparameter *template-ht*
  (let ((template-ht (make-hash-table :test #'eq)))
    (setf (gethash :serif_font template-ht) "Noto Serif")
    (setf (gethash :sans_font template-ht) "Lato")
    (setf (gethash :tt_font template-ht) "Source Code Pro")
    template-ht))

(defun get-file-with-templates (script)
  ;; This allows us to do at least some basic server-side processing on
  ;; .html/.css files, e.g., for includes, etc.
  (vls-try-catch
   :try
   (b* (((when    (or (str::substrp "~" script)
                      (str::isubstrp ".." script)))
         (setf (hunchentoot:return-code*) hunchentoot:+http-forbidden+)
         (cl-user::format nil "<html><body><h1>Forbidden</h1><h3>Request not allowed: ~a</h3></body></html>~%" script))

        (docroot  (uiop:native-namestring (hunchentoot:acceptor-document-root hunchentoot:*acceptor*)))
        (fullpath (oslib::catpath docroot script))

        ((unless (b* ((state acl2::*the-live-state*)
                      ((mv err ans ?state) (oslib::regular-file-p fullpath)))
                   (and (not err) ans)))
         (setf (hunchentoot:return-code*) hunchentoot:+http-not-found+)
         (cl-user::format nil "<html><body><h1>Error 404</h1><h3>File not found: ~a</h3></body></html>~%" fullpath))

        (html-template:*value-access-function* #'gethash)
        (template (html-template:create-template-printer (pathname fullpath))))

     (with-output-to-string (stream)
                            (html-template:fill-and-print-template template *template-ht* :stream stream)))
   :catch errmsg))

(defun request-html-file ()
  (setf (hunchentoot:content-type*) "text/html")
  (get-file-with-templates (hunchentoot:script-name*)))

(defun request-css-file ()
  (setf (hunchentoot:content-type*) "text/css")
  (get-file-with-templates (hunchentoot:script-name*)))

(let ((vl-server nil))

  (defun stop ()
    (when vl-server
      (hunchentoot:stop vl-server)
      (setq vl-server nil))
    nil)

  (defun start-fn (port public-dir)
    (acl2::mf-multiprocessing t t)
    (maybe-start-support-threads)
    (when vl-server
      (stop))
    (let* ((state acl2::*the-live-state*)
           (port (or port
                     (b* (((mv ? port ?state) (getenv$ "FVQ_PORT" state))
                          (port-num (str::strval port))
                          ((when port-num)
                           port-num))
                       ;; Else, just use the default port
                       9999)))
           (public-dir (or public-dir
                           (oslib::catpath *browser-dir* "/public/")))
           (public-dir (if (str::strsuffixp "/" public-dir)
                           public-dir
                         (cat public-dir "/")))
           (server (make-instance 'hunchentoot:easy-acceptor
                                  :port port
                                  :document-root public-dir)))
      (setf (hunchentoot:acceptor-access-log-destination server)
            (oslib::catpath public-dir "access.out"))
      (setf html-template:*default-template-pathname* (pathname public-dir))
      (hunchentoot:start server)
      (cl-user::format t "; ----------------------------------------------------------------~%")
      (cl-user::format t ";~%")
      (cl-user::format t ";         Module Browser Started at http://localhost:~D/~%" port)
      (cl-user::format t ";~%")
      (cl-user::format t "; ----------------------------------------------------------------~%~%")
      (add-handlers)
      (setq vl-server server))
    nil))

(defun add-handlers ()

  (setf hunchentoot:*dispatch-table*
        (list (hunchentoot:create-regex-dispatcher ".*\.html$" 'request-html-file)
              (hunchentoot:create-regex-dispatcher ".*\.css$" 'request-css-file)
              'hunchentoot:dispatch-easy-handlers))

  (hunchentoot:define-easy-handler (root :uri "/") ()
    ;; Since *.html doesn't match /
    (setf (hunchentoot:content-type*) "text/html")
    (get-file-with-templates "index.html"))

  (vls-add-automatic-command-handlers)

  (hunchentoot:define-easy-handler (list-unloaded :uri "/list-unloaded") ()
    (setf (hunchentoot:content-type*) "application/json")
    (with-vls-bindings
      (vls-try-catch
       :try (b* ((scanned  (vls-scanned-translations *vls-transdb*))
                 (loaded   (vls-loaded-translations *vls-transdb*))
                 (unloaded (difference (mergesort scanned)
                                       (mergesort loaded)))
                 (ans      (vl-tnames-to-json unloaded)))
              ;;(er hard? 'list-unloaded "error checking test")
              (vls-success :json (bridge::json-encode ans)))
       :catch (vls-fail errmsg))))

  (hunchentoot:define-easy-handler (list-loaded :uri "/list-loaded") ()
    (setf (hunchentoot:content-type*) "application/json")
    (with-vls-bindings
      (vls-try-catch
       :try (b* ((ans (vl-tnames-to-json (vls-loaded-translations *vls-transdb*))))
              ;; (er hard? 'list-loaded "Error checking test")
              (vls-success :json (bridge::json-encode ans)))
       :catch (vls-fail errmsg))))

  (hunchentoot:define-easy-handler (load-model :uri "/load-model" :default-request-type :post)
    ((base  :parameter-type 'string)
     (model :parameter-type 'string))
    (setf (hunchentoot:content-type*) "application/json")
    (with-vls-bindings
      (vls-try-catch
       :try (b* ((tname (make-vl-tname :base base :model model))
                 ((when (vls-quick-get-model tname *vls-transdb*))
                  (cw "; Model loaded: ~s0/~s1.~%" base model)
                  (vls-success :json (bridge::json-encode (list (cons :status :loaded))))))
              (cw "; Model starting: ~s0/~s1.~%" base model)
              (vls-start-model-load tname *vls-transdb*)
              (vls-success :json (bridge::json-encode (list (cons :status :started)))))
       :catch (vls-fail errmsg))))
  )


#||

(in-package "VL2014")

(let ((model (vls-quick-get-model (make-vl-tname :base "2014-10-02-22-09"
                                                 :model "cns")
                                  *vls-transdb*))
      (state acl2::*the-live-state*))
  (progn$
   (assign :model model)
   nil))

(lp)

(defconsts (*data*) (@ :model))
(vls-data-p *data*)

||#
