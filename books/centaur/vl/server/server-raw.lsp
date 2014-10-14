; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")

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
  (sem  (ccl::make-semaphore))

  ;; LOCK must be acquired whenever a producer or consumer needs to modify DATA
  ;; to insert or extract a value.
  (lock (ccl::make-lock 'queue-lock))

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
  (ccl::with-lock-grabbed ((ts-queue-lock queue))
                          (setf (ts-queue-data queue)
                                (append (ts-queue-data queue) (list obj))))
  (ccl::signal-semaphore (ts-queue-sem queue))
  obj)

(defxdoc-raw ts-dequeue
  :parents (ts-queue)
  :short "@('(ts-dequeue queue)') safely removes and returns the oldest object
from a queue.  If no objects are available, it blocks until an object is
added.")

(defun ts-dequeue (queue)
  (declare (type ts-queue queue))
  (ccl::wait-on-semaphore (ts-queue-sem queue))
  (ccl::with-lock-grabbed
   ((ts-queue-lock queue))
   (let ((obj (car (ts-queue-data queue))))
     (setf (ts-queue-data queue)
           (cdr (ts-queue-data queue)))
     obj)))

(defxdoc-raw ts-queue-len
  :parents (ts-queue)
  :short "@('(ts-queue-len queue)') returns the current length of the data list
for @('queue').  It can be used at any time by any thread and never blocks.")

(defun ts-queue-len (queue)
  (declare (type ts-queue queue))
  (ccl::with-lock-grabbed
   ((ts-queue-lock queue))
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
  (scanned-lock (ccl::make-lock 'vls-transdb-scanned-lock))

  ;; LOADED is an alist mapping tnames to their contents (vls-data-p objects).
  ;; It is updated by the vls-loader-thread, and perhaps in the future by some
  ;; kind of vls-unloader-thread.  You must acquire LOADED-LOCK when accessing
  ;; or updating this field.  Note also that the proper way to get a new
  ;; translation loaded is to add it to the LOAD-QUEUE via VLS-REQUEST-LOAD.
  (loaded      nil)
  (loaded-lock (ccl::make-lock 'vls-transdb-loaded-lock))

  ;; LOAD-QUEUE is a TS-QUEUE that governs which translations are next to be
  ;; loaded by the loader thread.
  (load-queue  (make-ts-queue)))

(defparameter *vls-transdb* (make-vls-transdb))


(defun vls-scanner-thread (db &optional noloop)

; Runs forever.  Lightweight.  Occasionally updates the list of SCANNED
; translation names to keep it in sync with the file system.  We do this in a
; separate thread because NFS can occasionally be slow and we don't want
; clients to have to wait for it when they connect.

  (declare (type vls-transdb db))
  (let ((state acl2::*the-live-state*))
    (loop do
          (cl-user::format t "; vls-scanner-thread: scanning for new translations.~%")
          (handler-case
           (let ((new-scan (time$ (vl-scan-for-tnames state)
                                  :msg "; rescan: ~st sec, ~sa bytes~%")))
             (ccl::with-lock-grabbed ((vls-transdb-scanned-lock db))
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
  (vls-scanner-thread *vls-transdb* nil))



(defun vls-scanned-translations (db)

; Safely access the list of translations that have been most recently returned
; by the scanner thread.

  (declare (type vls-transdb db))
  (ccl::with-lock-grabbed ((vls-transdb-scanned-lock db))
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

  (ccl::with-lock-grabbed
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
         (trans    (acl2::unsound-read filename :hons-mode :always :verbosep t)))
    (unless (cwtime (vl-translation-p trans))
      (cl-user::format t "; vls-load-translation: invalid translation data!~%")
      (return-from vls-load-translation nil))
    (let* ((data (vls-data-from-translation trans)))
      (ccl::with-lock-grabbed
       ((vls-transdb-loaded-lock db))
       (when (assoc-equal tname (vls-transdb-loaded db))
         (error "translation should not yet be loaded"))
       (setf (vls-transdb-loaded db)
             (acons tname data (vls-transdb-loaded db))))))

  (acl2::hons-summary)
  ;; this used to be okay, but with the new memoize table analysis, we
  ;; end up causing hash table ownership problems if we try to analyze
  ;; memory in the loader thread.

  ;; (acl2::hons-analyze-memory nil)
  )

(defun vls-loader-thread (db)

; Runs forever.  Tries to load any translations that are added to the load
; queue.

  (declare (type vls-transdb db))
  (let ((acl2::*default-hs* (acl2::hl-hspace-init
                             ;; 1 million strings seems sufficient
                             :str-ht-size (* 1000 1000)
                             ;; 500 million addr-ht seems sufficient.
                             :addr-ht-size (* 500 1000 1000)
                             )))
    (cl-user::format t "; vls-loader-thread hons space allocated~%")
    (loop do
          (handler-case
           (let ((tname (ts-dequeue (vls-transdb-load-queue db))))
             (vls-load-translation tname db))))))

           ;; (error (condition)
           ;;        (cl-user::format t "Ignoring unexpected error in ~
           ;;                           vls-loader-thread: ~a~%"
           ;;                         condition))))))






;(acl2::mf-multiprocessing t)
(setq acl2::*enable-multithreaded-memoization* t)
(acl2::rememoize-all)

(let ((support-started nil))
  (defun maybe-start-support-threads ()
    (unless support-started
      (ccl::process-run-function (list :name "vls-scanner-thread"
                                       :stack-size  (* 8  (expt 2 20))  ;; 8 MB
                                       :vstack-size (* 16 (expt 2 20))  ;; 16 MB
                                       :tstack-size (* 8  (expt 2 20))  ;; 8 MB
                                       )
                                 'vls-scanner-thread
                                 *vls-transdb*)
      (ccl::process-run-function (list :name "vls-loader-thread"
                                       :stack-size  (* 8 (expt 2 20))   ;; 8 MB
                                       :vstack-size (* 128 (expt 2 20)) ;; 128 MB
                                       :tstack-size (* 8 (expt 2 20))   ;; 8 MB
                                       )
                                 'vls-loader-thread
                                 *vls-transdb*)
      (setq support-started t))))

(defun vls-loaded-translations (db)
  (alist-keys
   (ccl::with-lock-grabbed ((vls-transdb-loaded-lock db))
     (vls-transdb-loaded db))))


(let ((vl-server nil))

  (defun stop ()
    (when vl-server
      (hunchentoot:stop vl-server)
      (setq vl-server nil))
    nil)

  (defun start-fn (port public-dir)
    (maybe-start-support-threads)
    (when vl-server
      (stop))
    (let* ((port (or port
                     (b* (((mv ? port state) (getenv$ "FVQ_PORT" state))
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
      (hunchentoot:start server)
      (cl-user::format t "; ----------------------------------------------------------------~%")
      (cl-user::format t ";~%")
      (cl-user::format t ";         Module Browser Started at http://localhost:~D/~%" port)
      (cl-user::format t ";~%")
      (cl-user::format t "; ----------------------------------------------------------------~%~%")
      (add-handlers)
      (setq vl-server server))
    nil))


(defmacro with-handler-bindings (&rest forms)
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



(defun vls-quick-get-model (tname db)
  (ccl::with-lock-grabbed
    ;; If it's already loaded, don't try to load it again.
    ((vls-transdb-loaded-lock db))
    (let ((pair (assoc-equal tname (vls-transdb-loaded db))))
      (and pair
           (cdr pair)))))

(defun vls-start-model-load (tname db)
  (ccl::with-lock-grabbed
    ((vls-transdb-loaded-lock db))
    (ts-enqueue tname (vls-transdb-load-queue db))))

(defun add-handlers ()

  (hunchentoot:define-easy-handler (list-unloaded :uri "/list-unloaded") ()
    (setf (hunchentoot:content-type*) "application/json")
    (let* ((scanned  (vls-scanned-translations *vls-transdb*))
           (loaded   (vls-loaded-translations *vls-transdb*))
           (unloaded (difference (mergesort scanned)
                                 (mergesort loaded)))
           (ans      (vl-tnames-to-json unloaded)))
      (bridge::json-encode (list (cons :value ans)))))

  (hunchentoot:define-easy-handler (list-loaded :uri "/list-loaded") ()
    (setf (hunchentoot:content-type*) "application/json")
    (let ((ans (vl-tnames-to-json (vls-loaded-translations *vls-transdb*))))
      (bridge::json-encode (list (cons :value ans)))))

  (hunchentoot:define-easy-handler (load-model :uri "/load-model" :default-request-type :post)
    ((base  :parameter-type 'string)
     (model :parameter-type 'string))
    (setf (hunchentoot:content-type*) "application/json")
    (let ((tname (make-vl-tname :base base :model model)))
      (if (vls-quick-get-model tname *vls-transdb*)
          (bridge::json-encode (list (cons :status :loaded)))
        (progn
          (vls-start-model-load tname *vls-transdb*)
          (bridge::json-encode (list (cons :status :started)))))))

  (hunchentoot:define-easy-handler (load-model :uri "/load-model" :default-request-type :post)
    ((base  :parameter-type 'string)
     (model :parameter-type 'string))
    (setf (hunchentoot:content-type*) "application/json")
    (let ((tname (make-vl-tname :base base :model model)))
      (if (vls-quick-get-model tname *vls-transdb*)
          (bridge::json-encode (list (cons :status :loaded)))
        (progn
          (vls-start-model-load tname *vls-transdb*)
          (bridge::json-encode (list (cons :status :started)))))))

  (hunchentoot:define-easy-handler (get-summary :uri "/get-summary")
    ((base     :parameter-type 'string)
     (model    :parameter-type 'string)
     (origname :parameter-type 'string))
    (setf (hunchentoot:content-type*) "application/json")
    (b* ((tname (make-vl-tname :base base :model model))
         (data (vls-quick-get-model tname *vls-transdb*))
         ((unless data)
          (bridge::json-encode (list (cons :error "Invalid model")))))
      (bridge::json-encode (list (cons :error nil)
                                 (cons :value (vls-get-summary origname data))))))

  (hunchentoot:define-easy-handler (get-summaries :uri "/get-summaries")
    ((base  :parameter-type 'string)
     (model :parameter-type 'string))
    (setf (hunchentoot:content-type*) "application/json")
    (b* ((tname (make-vl-tname :base base :model model))
         (data (vls-quick-get-model tname *vls-transdb*))
         ((unless data)
          (bridge::json-encode (list (cons :error "Invalid model"))))
         ((vls-data data)))
      (bridge::json-encode (list (cons :error nil)
                                 (cons :value (vl-descriptionlist-summaries
                                               (alist-vals data.orig-descalist)))))))

  (hunchentoot:define-easy-handler (get-parents :uri "/get-parents")
    ((base     :parameter-type 'string)
     (model    :parameter-type 'string)
     (origname :parameter-type 'string))
    (setf (hunchentoot:content-type*) "application/json")
    (b* ((tname (make-vl-tname :base base :model model))
         (data (vls-quick-get-model tname *vls-transdb*))
         ((unless data)
          (bridge::json-encode (list (cons :error "Invalid model")))))
      (bridge::json-encode (list (cons :error nil)
                                 (cons :value (vls-get-parents origname data))))))

  (hunchentoot:define-easy-handler (get-children :uri "/get-children")
    ((base     :parameter-type 'string)
     (model    :parameter-type 'string)
     (origname :parameter-type 'string))
    (setf (hunchentoot:content-type*) "application/json")
    (b* ((tname (make-vl-tname :base base :model model))
         (data (vls-quick-get-model tname *vls-transdb*))
         ((unless data)
          (bridge::json-encode (list (cons :error "Invalid model")))))
      (bridge::json-encode (list (cons :error nil)
                                 (cons :value (vls-get-children origname data))))))

  (hunchentoot:define-easy-handler (get-origsrc :uri "/get-origsrc")
    ((base  :parameter-type 'string)
     (model :parameter-type 'string)
     (origname :parameter-type 'string))
    (setf (hunchentoot:content-type*) "text/html")
    (with-handler-bindings
      (b* ((tname (make-vl-tname :base base :model model))
           (data (vls-quick-get-model tname *vls-transdb*))
           ((unless data)
            "<p>Invalid model</p>"))
        (vls-get-origsrc origname data))))

  (hunchentoot:define-easy-handler (get-plain :uri "/get-plainsrc")
    ((base  :parameter-type 'string)
     (model :parameter-type 'string)
     (origname :parameter-type 'string))
    (setf (hunchentoot:content-type*) "text/plain")
    (with-handler-bindings
      (b* ((tname (make-vl-tname :base base :model model))
           (data (vls-quick-get-model tname *vls-transdb*))
           ((unless data)
            "Invalid model"))
        (vls-get-plainsrc origname data))))

  (hunchentoot:define-easy-handler (get-desctypes :uri "/get-desctypes")
    ((base  :parameter-type 'string)
     (model :parameter-type 'string))
    (setf (hunchentoot:content-type*) "text/html")
    (with-handler-bindings
      (b* ((tname (make-vl-tname :base base :model model))
           (data (vls-quick-get-model tname *vls-transdb*))
           ((unless data) "Invalid model."))
        (bridge::json-encode (list (cons :error nil)
                                   (cons :value (vls-data->descriptions/types data)))))))

  (hunchentoot:define-easy-handler (get-describe :uri "/describe")
    ((base     :parameter-type 'string)
     (model    :parameter-type 'string)
     (origname :parameter-type 'string)
     (what     :parameter-type 'string))
    (setf (hunchentoot:content-type*) "text/html")
    (with-handler-bindings
      (b* ((tname (make-vl-tname :base base :model model))
           (data (vls-quick-get-model tname *vls-transdb*))
           ((unless data) "Invalid model."))
        (vls-describe data origname what))))

  (hunchentoot:define-easy-handler (get-loc :uri "/loc")
    ((base     :parameter-type 'string)
     (model    :parameter-type 'string)
     (file     :parameter-type 'string)
     (line     :parameter-type 'string)
     (col      :parameter-type 'string))
    (setf (hunchentoot:content-type*) "text/html")
    (with-handler-bindings
      (b* ((tname (make-vl-tname :base base :model model))
           (data (vls-quick-get-model tname *vls-transdb*))
           ((unless data) "Invalid model.")
           (line (str::strval line))
           (col  (str::strval col))
           ((unless (posp line)) "Invalid line number.")
           ((unless (natp col)) "Invalid column number."))
        (vls-showloc data file line col))))

  (hunchentoot:define-easy-handler (get-porttable :uri "/porttable")
    ((base       :parameter-type 'string)
     (model      :parameter-type 'string)
     (origname   :parameter-type 'string))
    (setf (hunchentoot:content-type*) "text/html")
    (with-handler-bindings
      (b* ((tname (make-vl-tname :base base :model model))
           (data  (vls-quick-get-model tname *vls-transdb*))
           ((unless data) "Invalid model."))
        (vls-port-table data origname))))

  )


#||

(in-package "VL")

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
