#|$ACL2s-Preamble$;
(ld ;; Newline to fool ACL2/cert.pl dependency scanner 
"acl2s-pkg.lsp")

(acl2::begin-book t :ttags ((:acl2s-graphics)));$ACL2s-Preamble$|#


(in-package "ACL2")

(include-book "make-event/inline-book" :dir :system)
(inline-book "graphics-basis" :ttags ((:acl2s-graphics)))

(set-verify-guards-eagerness 2)

(defun assoc-cdr-or-nil (x alist)
  (declare (xargs :guard (and (eqlablep x)
                              (alistp alist))))
  (let ((v (assoc x alist)))
    (cond ((consp v)
           (cdr v))
          (t nil))))

(defun timer-handler-fnp (f world)
  (declare (xargs :guard (plist-worldp world)))
  (and (symbolp f)
       (equal (fgetprop f 'stobjs-in nil world)
              '(nil))
       (equal (fgetprop f 'stobjs-out nil world)
              '(nil))))

(defun timer-handler-listp (l world)
  (declare (xargs :guard (plist-worldp world)))
  (or (null l)
      (and (consp l)
           (consp (car l))
           (natp (caar l))
           (timer-handler-fnp (cdar l) world)
           (timer-handler-listp (cdr l) world))))

(defun key-handlerp (f world)
  (declare (xargs :guard (plist-worldp world)))
  (and (symbolp f)
       (equal (fgetprop f 'stobjs-in nil world)
              '(nil nil)) ; char * configuration
       (equal (fgetprop f 'stobjs-out nil world)
              '(nil))))

(defun key-handler-listp (l world)
  (declare (xargs :guard (plist-worldp world)))
  (or (null l)
      (and (consp l)
           (key-handlerp (car l) world)
           (key-handler-listp (cdr l) world))))

(defun click-handlerp (f world)
  (declare (xargs :guard (plist-worldp world)))
  (and (symbolp f)
       (equal (fgetprop f 'stobjs-in nil world)
              '(nil nil nil nil)) ; button * x * y * configuration
       (equal (fgetprop f 'stobjs-out nil world)
              '(nil))))

(defun click-handler-listp (l world)
  (declare (xargs :guard (plist-worldp world)))
  (or (null l)
      (and (consp l)
           (click-handlerp (car l) world)
           (click-handler-listp (cdr l) world))))

(defun configuration-presenterp (c world)
  (declare (xargs :guard (plist-worldp world)))
  (and (symbolp c)
       (equal (fgetprop c 'stobjs-in nil world)
              '(nil nil)) ; configuration * (blank) presentation 
       (equal (fgetprop c 'stobjs-out nil world)
              '(nil)))) ; presentation

(table graphics-frontend nil nil
       :guard
       (cond ((eq key 'timer-handlers)
              (timer-handler-listp val world))
             ((eq key 'key-handlers)
              (key-handler-listp val world))
             ((eq key 'click-handlers)
              (click-handler-listp val world))
             ((eq key 'configuration-presenter)
              (configuration-presenterp val world))
             ((eq key 'initial-configuration)
              t)
             (t nil)))

(defmacro add-timer-handler (delay-ms f)
  (let ((func (cond ((symbolp f)
                     f)
                    ((and (consp f)
                          (= (len f) 2)
                          (eq (first f) 'quote))
                     (second f))
                    (t
                     (er hard 'add-timer-handler
                         "The second argument must be a (possibly quoted) symbol for the handler routine.  ~x0 is not."
                         f))))
        (delay (cond ((natp delay-ms)
                      delay-ms)
                     ((and (consp delay-ms)
                           (= (len delay-ms) 2)
                           (eq (first delay-ms) 'quote))
                      (second delay-ms))
                     (t
                      (er hard 'add-timer-handler
                          "The first argument must by a (possibly quoted) natural number for milliseconds of delay.  ~x0 is not."
                          delay-ms)))))
    `(progn (value-triple
             (or (timer-handler-fnp ',func (w state))
                 (if (fgetprop ',func 'symbol-class nil (w state))
                   (er hard 'add-timer-handler
                       "The function specified must take in one argument (current configuration) and return one result (new configuration).  ~x0 does not."
                       ',func)
                   (er hard 'add-timer-handler
                       "~x0 is not a function in the current ACL2 world."
                       ',func))))
            (table graphics-frontend 'timer-handlers
                   (append (assoc-cdr-or-nil 'timer-handlers (table-alist 'graphics-frontend world))
                           (list (cons ',delay ',func))))
            (value-triple (cons ',delay ',func))))) 

(defmacro add-key-handler (f)
  (let ((func (cond ((symbolp f)
                     f)
                    ((and (consp f)
                          (= (len f) 2)
                          (eq (first f) 'quote))
                     (second f))
                    (t
                     (er hard 'add-key-handler
                         "The argument must be a (possibly quoted) symbol for the handler routine.  ~x0 is not."
                         f)))))
    `(progn (value-triple
             (or (key-handlerp ',func (w state))
                 (if (fgetprop ',func 'symbol-class nil (w state))
                   (er hard 'add-key-handler
                       "The function specified must take in two arguments (char * configuration) and return one result (new configuration).  ~x0 does not."
                       ',func)
                   (er hard 'add-key-handler
                       "~x0 is not a function in the current ACL2 world."
                       ',func))))
            (table graphics-frontend 'key-handlers
                   (let ((old (assoc-cdr-or-nil 'key-handlers (table-alist 'graphics-frontend world))))
                     (if (member-eq ',func old)
                       old
                       (append old (list ',func)))))
            (value-triple ',func))))

(defmacro add-click-handler (f)
  (let ((func (cond ((symbolp f)
                     f)
                    ((and (consp f)
                          (= (len f) 2)
                          (eq (first f) 'quote))
                     (second f))
                    (t
                     (er hard 'add-click-handler
                         "The argument must be a (possibly quoted) symbol for the handler routine.  ~x0 is not."
                         f)))))
    `(progn (value-triple
             (or (click-handlerp ',func (w state))
                 (if (fgetprop ',func 'symbol-class nil (w state))
                   (er hard 'add-click-handler
                       "The function specified must take in four arguments (button-number * x-pos * y-pos * configuration) and return one result (new configuration).  ~x0 does not."
                       ',func)
                   (er hard 'add-click-handler
                       "~x0 is not a function in the current ACL2 world."
                       ',func))))
            (table graphics-frontend 'click-handlers
                   (let ((old (assoc-cdr-or-nil 'click-handlers (table-alist 'graphics-frontend world))))
                     (if (member-eq ',func old)
                       old
                       (append old (list ',func)))))
            (value-triple ',func))))

(defmacro set-configuration-presenter (f)
  (let ((func (cond ((symbolp f)
                     f)
                    ((and (consp f)
                          (= (len f) 2)
                          (eq (first f) 'quote))
                     (second f))
                    (t
                     (er hard 'set-configuration-presenter
                         "The argument must be a (possibly quoted) symbol for the handler routine.  ~x0 is not."
                         f)))))
    `(progn (value-triple
             (or (configuration-presenterp ',func (w state))
                 (if (fgetprop ',func 'symbol-class nil (w state))
                   (er hard 'set-configuration-presenter
                       "The function specified must take in two arguments (configuration * empty-presentation) and return one result (new-presentation).  ~x0 does not."
                       ',func)
                   (er hard 'set-configuration-presenter
                       "~x0 is not a function in the current ACL2 world."
                       ',func))))
            (table graphics-frontend 'configuration-presenter ',func)
            (value-triple ',func))))
  
(defmacro set-initial-configuration (val)
  `(progn (value-triple ,val) ; sensible error message for bad construction
          (table graphics-frontend 'initial-configuration ,val)
          (value-triple ,val))) ; for return value



;;***************** presentation stuff ****************;;

;; presentation is (cons status_string list_of_actions)
(defun presentationp (x)
  (and (consp x)
       (stringp (car x))
       (true-listp (cdr x))))

(defun empty-presentation () (cons "" nil))

(defun set-status-bar (str presentation)
  (declare (xargs :guard (and (presentationp presentation)
                              (stringp str))))
  (cons str
        (cdr presentation)))

(defun draw-line (x1 y1 x2 y2 color presentation)
  (declare (xargs :guard (and (presentationp presentation)
                              (rationalp x1)
                              (rationalp y1)
                              (rationalp x2)
                              (rationalp y2))))
  (list* (car presentation)
         (list :drawline x1 y1 x2 y2 color)
         (cdr presentation)))

(defun outline-oval (x y w h color presentation)
  (declare (xargs :guard (and (presentationp presentation)
                              (rationalp x)
                              (rationalp y)
                              (rationalp w)
                              (rationalp h))))
  (list* (car presentation)
         (list :drawoval x y w h color nil)
         (cdr presentation)))

(defun outline-oval-centered (x y w h color presentation)
  (declare (xargs :guard (and (presentationp presentation)
                              (rationalp x)
                              (rationalp y)
                              (rationalp w)
                              (rationalp h))))
  (outline-oval (- x (/ w 2)) (- y (/ h 2)) w h color presentation))

(defun fill-oval (x y w h color presentation)
  (declare (xargs :guard (and (presentationp presentation)
                              (rationalp x)
                              (rationalp y)
                              (rationalp w)
                              (rationalp h))))
  (list* (car presentation)
         (list :drawoval x y w h nil color)
         (cdr presentation)))

(defun fill-oval-centered (x y w h color presentation)
  (declare (xargs :guard (and (presentationp presentation)
                              (rationalp x)
                              (rationalp y)
                              (rationalp w)
                              (rationalp h))))
  (fill-oval (- x (/ w 2)) (- y (/ h 2)) w h color presentation))


(defun outline-rect (x y w h color presentation)
  (declare (xargs :guard (and (presentationp presentation)
                              (rationalp x)
                              (rationalp y)
                              (rationalp w)
                              (rationalp h))))
  (list* (car presentation)
         (list :drawrect x y w h nil color)
         (cdr presentation)))

(defun outline-rect-centered (x y w h color presentation)
  (declare (xargs :guard (and (presentationp presentation)
                              (rationalp x)
                              (rationalp y)
                              (rationalp w)
                              (rationalp h))))
  (outline-rect (- x (/ w 2)) (- y (/ h 2)) w h color presentation))


(defun fill-rect (x y w h color presentation)
  (declare (xargs :guard (and (presentationp presentation)
                              (rationalp x)
                              (rationalp y)
                              (rationalp w)
                              (rationalp h))))
  (list* (car presentation)
         (list :drawrect x y w h nil color)
         (cdr presentation)))

(defun fill-rect-centered (x y w h color presentation)
  (declare (xargs :guard (and (presentationp presentation)
                              (rationalp x)
                              (rationalp y)
                              (rationalp w)
                              (rationalp h))))
  (fill-rect (- x (/ w 2)) (- y (/ h 2)) w h color presentation))

(defun center-image (x y path presentation)
  (declare (xargs :guard (and (presentationp presentation)
                              (rationalp x)
                              (rationalp y)
                              (stringp path))))

  (list* (car presentation)
         (list :putimage x y path :center)
         (cdr presentation)))

(defun put-image (x y w h path presentation)
  (declare (xargs :guard (and (presentationp presentation)
                              (rationalp x)
                              (rationalp y)
                              (rationalp w)
                              (rationalp h)
                              (stringp path))))
  (list* (car presentation)
         (list :putimage x y path :topleft w h)
         (cdr presentation)))

(defun center-text (x y text h color presentation)
  (declare (xargs :guard (and (presentationp presentation)
                              (rationalp x)
                              (rationalp y)
                              (rationalp h)
                              (stringp text))))
  (list* (car presentation)
         (list :puttext x y text h color :center)
         (cdr presentation)))

(defun put-text (x y text h color presentation)
  (declare (xargs :guard (and (presentationp presentation)
                              (rationalp x)
                              (rationalp y)
                              (rationalp h)
                              (stringp text))))
  (list* (car presentation)
         (list :puttext x y text h color :topleft)
         (cdr presentation)))


(defconst *window-target* '(window))

(defun apply-presentation (presentation graphics)
  (declare (xargs :guard (presentationp presentation)
                  :stobjs graphics))
  (let* ((graphics
          (push-graphics-op
           (list *window-target* :setstatus (car presentation))
           graphics))
         (graphics
          (push-graphics-op
           (list *window-target* :setpresentation (reverse (cdr presentation)))
           graphics)))
    graphics))


;; *************** the glue ************** ;;

(program)
(set-state-ok t)

(defun timer-handler-list-to-alist (timer-handlers)
  (if (endp timer-handlers)
    nil
    (cons (cons (intern (coerce
                                  (append
                                   (coerce "TIMER" 'list)
                                   (explode-atom (len timer-handlers) 10))
                                  'string)
                                 "COMMON-LISP")
                (car timer-handlers))
          (timer-handler-list-to-alist (cdr timer-handlers)))))


(defun generate-start-timers (timer-handler-alist)
  (if (endp timer-handler-alist)
    nil
    (list* `(graphics
             (push-graphics-op
              '(nil :create :timer ,(caar timer-handler-alist))
              graphics))
           `(graphics
             (push-graphics-op
              '((,(caar timer-handler-alist)) :repeat ,(cadar timer-handler-alist))
              graphics))
           (generate-start-timers (cdr timer-handler-alist)))))

(defun generate-present-config (func)
  `((graphics (apply-presentation ,(if func
                                     `(,func config (empty-presentation))
                                     'config)
                                  graphics))))


(defun generate-apply-click-handlers (click-handlers)
  ;; given ev and config
  (if (consp click-handlers)
    `(,(car click-handlers)
      (third ev)
      (fourth ev)
      (cddddr ev)
      ,(generate-apply-click-handlers (cdr click-handlers)))
    'config))

(defun generate-apply-key-handlers (key-handlers)
  ;; given ev and config
  (if (consp key-handlers)
    `(,(car key-handlers)
      (cddr ev)
      ,(generate-apply-key-handlers (cdr key-handlers)))
    'config))

(defun generate-apply-timer-handlers (timer-handler-alist)
  ;; given ev and config
  (if (consp timer-handler-alist)
    `(if (eq (caar ev) ',(caar timer-handler-alist))
       (,(cddar timer-handler-alist) config)
       ,(generate-apply-timer-handlers (cdr timer-handler-alist)))
    'config))


(defmacro big-bang (&optional (width '0) (height '0))
  (declare (xargs :guard (and (natp width)
                              (natp height))))
  `(er-progn
    (ld
     (let* ((frontend-alist (table-alist 'graphics-frontend
                                         (w state)))
            (timer-handler-alist
             (timer-handler-list-to-alist
              (assoc-cdr-or-nil 'timer-handlers
                                frontend-alist)))
            (key-handlers
             (reverse (assoc-cdr-or-nil 'key-handlers frontend-alist)))
            (click-handlers
             (reverse (assoc-cdr-or-nil 'click-handlers frontend-alist)))
            (configuration-presenter
             (assoc-cdr-or-nil 'configuration-presenter frontend-alist))
            (initial-configuration
             (assoc-cdr-or-nil 'initial-configuration frontend-alist)))
       (if (not configuration-presenter)
         `((er soft 'big-bang
               "No \"configuration presenter\" registered.  Please register one with ~x0."
               'set-configuration-presenter))
         `((cw "======================================================================~%~
                Initial configuration: ~x0~%~
                Configuration presenter function: ~x1~%~
                Click handlers: ~&2~%~
                Key handlers: ~&3~%~
                Timer handlers/timeouts: ~&4~%~
                ======================================================================~%"
             '',initial-configuration
             ',configuration-presenter
             ',click-handlers
             ',key-handlers
             ',timer-handler-alist)
           (with-output
            :off summary
            (defun big-bang-loop (config graphics)
              (declare (xargs :mode :program
                              :stobjs graphics))
              (mv-let (ev graphics)
                      (pop-graphics-event graphics)
                      (if (or (not (consp ev))
                              (not (consp (cdr ev)))
                              (eq (cadr ev) :CLOSED))
                        graphics ; done
                        (let* ((new-config
                                (cond ((eq (cadr ev) :click)
                                       ,(generate-apply-click-handlers click-handlers))
                                      ((eq (cadr ev) :key)
                                       ,(generate-apply-key-handlers key-handlers))
                                      ((eq (cadr ev) :tick)
                                       ,(generate-apply-timer-handlers timer-handler-alist))
                                      (t ; wtf?
                                       (prog2$ (cw "Unexpected event: ~x0~%" ev)
                                               config))))
                               (graphics 
                                (if (equal config new-config)
                                  graphics
                                  (let* ((config new-config)
                                         ,@(generate-present-config configuration-presenter))
                                    graphics)))
                               (graphics
                                (big-bang-loop new-config graphics)))
                          graphics)))))
           (with-output
            :off summary
            (defun big-bang-fn (graphics)
              (declare (xargs :mode :program
                              :stobjs graphics))
              (let*
                ((width (if (zp ',',width)
                          500
                          ',',width))
                 (height (if (zp ',',height)
                           width
                           ',',height))
                 (graphics
                  (push-graphics-op `(nil :create :scalable-presentation-window
                                          ,(car *window-target*)
                                          "ACL2 Graphics Window"
                                          ,width
                                          ,height)
                                    graphics))
                 (graphics
                  (push-graphics-op `(,*window-target* :show)
                                    graphics))
                 (config ',initial-configuration)
                 ,@(generate-present-config configuration-presenter)
                 ,@(generate-start-timers timer-handler-alist)
                 (graphics (big-bang-loop config graphics)))
                graphics)))
           (big-bang-fn graphics))))
       ;;:ld-pre-eval-print t
       :ld-verbose nil :ld-prompt nil :ld-post-eval-print nil)
     (mv (or (cw "(graphics interaction aborted)~%") t)
         :invisible state)))
