(in-package "ACL2S-INTERFACE-INTERNAL")

;; Borrwed from centaur/vl/server/server-raw.lsp, which itself was
;; borrowed from the SBCL manual's section on "Defining Constants"
;; This is neccesary under SBCL, but it may or may not be neccesary
;; under other CL implementations.
;; Added eval-when so that things work properly in CCL.
(defmacro define-constant (name value &optional doc)
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     (defconstant ,name (if (boundp ',name) (symbol-value ',name) ,value)
       ,@(when doc (list doc)))))

;; Define a dynamic variable. This is a macro because we need to add
;; eval-when around all of these so that things work properly in CCL.
(defmacro define-var (name value &optional doc)
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     (defparameter ,name ,value ,@(when doc (list doc)))))

;; Some utilities

;; Removes a property with a given key from a keyword argument list
;; non-destructively
(defun remove-prop (plist key)
  (cond
   ((endp plist) nil)
   ((endp (cdr plist)) nil) ;; just in case it's not even-length
   ((eq key (car plist)) (remove-prop (cddr plist) key))
   (t (cons (car plist)
	    (cons (cadr plist) (remove-prop (cddr plist) key))))))

(defun remove-props (plist keys)
  (if (endp keys)
      plist
    (remove-props (remove-prop plist (car keys))
		  (cdr keys))))

;; Get the value associated with a key in a keyword argument list.
;; Returns two values, where the first is the associated value if it
;; exists and nil otherwise, and the second is t if the key was found
;; in the plist and nil otherwise.
(defun get-prop (plist key)
  (cond
   ((endp plist) (values nil nil))
   ((endp (cdr plist)) (values nil nil)) ;; just in case it's not even-length
   ((eq key (car plist)) (values (cadr plist) t))
   (t (get-prop (cddr plist) key))))

;; Get the value associated with the given key in the given ACL2 table.
(declaim (ftype (function (symbol symbol) *) get-table-value))
(defun get-table-value (table key)
  (cdr (acl2::assoc-equal key (acl2::getpropc table 'acl2::table-alist nil (acl2::w acl2::state)))))

;; Get the prover-step-limit that ACL2 would have used for a top-level
;; evaluation.
(defun get-prover-step-limit ()
  (or (get-table-value 'acl2::acl2-defaults-table :step-limit)
      acl2::*default-step-limit*))

#| 

 This is a super-ugly hack to enable us to control and capture some of
 ACL2's output.

 Some ACL2 code (for example, ACL2s) uses the macro cw ("comment
 window") to print out information. ld's :standard-co option does not
 redirect the output from these calls, and there may be no other way
 to stop the offending library from calling CW. See
 https://github.com/acl2/acl2/issues/1008 for more information as to
 why this is the case.

 We work around this by saving the original definition of one of the
 functions that the cw macro calls, and defining our own version of
 the function that behaves differently based on whether the user has
 indicated they want to capture and/or hide ACL2 output. This is
 potentially dangerous (because we're redefining one of ACL2's
 internal functions) but is effective.

|#

;; We will end up creating a bunch of temporary streams. It is likely
;; possible to reuse many of these streams, but this feature is not
;; yet implemented. Thus, we keep track of the temporary streams we
;; create during a query so that we can close them after the query is
;; complete.
(define-var *temporary-streams* nil "A list of streams to close after the current query has completed.")

(eval-when (:compile-toplevel :load-toplevel :execute)
  ;; Make an ACL2 output channel, which consists of a symbol with some
  ;; well-known properties attached to it.
  (defun mk-output-channel (stream state &key (type :character) (temporary t))
    (declare (ignore state))
    (let ((name (gentemp)))
      (setf (get name acl2::*open-output-channel-type-key*) type)
      (setf (get name acl2::*open-output-channel-key*) stream)
      (when temporary (push name *temporary-streams*))
      name)))

;; Note that I'm entirely sidestepping ACL2's system for keeping track
;; of open channels, so I wouldn't be surprised if this approach
;; breaks something. Below I include an implementation that uses
;; ACL2's interface for creating output channels, and then overwrites
;; the channel's stream property. This might also break something, but
;; at least the channels would be tracked by ACL2.

;; I chose to use the first approach as it does not require messing
;; around with state.

#|
(defun mk-output-channel (stream state &key (type :character))
  (let ((channel (acl2::open-output-channel :string type state)))
    (setf (get channel 'old-stream) (get channel acl2::*open-output-channel-key*))
    (setf (get channel acl2::*open-output-channel-key*) stream)
    channel))
|#

;; This will be called after each high-level query provided in this
;; file. This is intended to clean up the large number of temporary
;; broadcast streams we'll be creating.
(defun cleanup-streams ()
  (loop for stream in *temporary-streams*
        do (close (get stream acl2::*open-output-channel-key*)))
  (setf *temporary-streams* nil))

;; TODO (drew): we should memoize broadcast streams, since it is
;; unlikely that the "original" standard-co, proofs-co, or
;; comment-window-co will be changing often. This should be an easy
;; win for improved performance.

;; This is the stream to which we will be sending any output that the
;; user wants us to collect.
(define-var *capture-output-stream* (make-string-output-stream))
;; We don't want to automatically dispose of *capture-output-channel*,
;; since it is intended to be used for the duration of this process'
;; life.
(define-var *capture-output-channel* (mk-output-channel *capture-output-stream* acl2::*the-live-state* :temporary nil))

;; We need a channel that will dispose of any input sent to it.
(define-var *empty-output-stream* (make-broadcast-stream))
(define-var *empty-output-channel* (mk-output-channel *empty-output-stream* acl2::*the-live-state* :temporary nil))

(define-var *disable-comment-window-printing* nil
  "If non-nil, disable all printing to the comment window")
(define-var *capture-output* nil
  "If non-nil, capture any ACL2 output to the comment window, standard-co, or proofs-co.")

;; Give ourselves the ability to replace the value returned by
;; comment-window-co. Depending on the combination of *capture-output*
;; and *disable-comment-window-printing*, we may want to return one of
;; several different values.
#-ACL2S-INTERFACE-NO-OVERWRITE
(define-constant +old-comment-window-co+ #'acl2::comment-window-co)
#-ACL2S-INTERFACE-NO-OVERWRITE
(defun acl2::comment-window-co ()
  (cond (;; If we want to capture output and also not print it
         ;; normally, we just return our capture channel.
         (and *capture-output* *disable-comment-window-printing*)
         *capture-output-channel*)
        ;; In this case, we want to both capture the output and print
        ;; it normally. So, we will create a channel backed by a
        ;; broadcast stream that sends output to both the capture
        ;; channel and the normal channel.
        (*capture-output*
         (let* ((normal-channel (funcall +old-comment-window-co+))
                (broadcast-stream (make-broadcast-stream *capture-output-stream* (get normal-channel acl2::*open-output-channel-key*))))
           (mk-output-channel broadcast-stream acl2::*the-live-state*)))
        ;; We don't want to capture any output and we don't want any
        ;; comment window printing, so redirect to the empty channel.
        (*disable-comment-window-printing* *empty-output-channel*)
        ;; Otherwise, we want to behave as normal, so we just call the
        ;; old comment-window-co
        (t (funcall +old-comment-window-co+))))

;; Returns the output captured since the last get-captured-output, and
;; clears the captured output.
(defun get-captured-output ()
  (get-output-stream-string *capture-output-stream*))

;; Flags for ld that turn off most of its output. Our functions for
;; performing high-level queries treat standard-co and proofs-co
;; specially, so this set of flags does not touch those options.
(define-constant LD-QUIET-FLAGS
  '(:ld-pre-eval-print nil
    :ld-post-eval-print nil
    :ld-redefinition-action nil
    :ld-prompt nil
    :ld-verbose nil))

;; Flags for ld that turn off most of its output, including
;; redirecting standard-co and proofs-co to a "black hole" that will
;; consume all output.
;; This is probably what you want if you're using ld "internally".
(define-var LD-REALLY-QUIET-FLAGS
  (append LD-QUIET-FLAGS `(:standard-co ',*empty-output-channel* :proofs-co ',*empty-output-channel*)))

;;(defun ld-kwd-args-to-ld-special-bindings (args)
;;  (loop for kwd-name in args by #'cddr
;;        for kwd-val in (cdr args) by #'cddr
;;        collect (cons (intern (symbol-name kwd-name) "ACL2") kwd-val)))

;; Names of "LD specials".
;; These are an approximation of the valid
;; options to pass to ld-fn.
;;(define-constant +LD-SPECIALS+ (mapcar #'car acl2::(f-get-ld-specials state)))

;; Call ld with the given query and LD special bindings.
;; This allows us to set options using a list

;; We use ACL2's "with-suppression" macro to disable many warnings and
;; avoid package lock errors when a user submits a query with a symbol
;; in the function call position that does not have a function
;; definition. This is used in `lp` for the same purpose.
(defun ld-options (q options)
  ;; Ideally we would use `apply` instead of `eval` here. Unfortunately,
  ;; doing this would require us to replicate a lot of the keyword
  ;; argument handling code inside of LD's definition
  (eval `(acl2::with-suppression
          ;; CCL will complain if we don't bind state
          (let ((acl2::state acl2::*the-live-state*))
            (acl2::ld ',q ,@options)))))

;; These variables save the values of settings at the time quiet mode
;; is enabled, so that we can restore them when quiet mode is
;; disabled. The default values are the default values for these
;; settings when this file is run.
(define-var *saved-inhibit-output-list* (acl2::@ acl2::inhibit-output-lst))
(define-var *saved-gag-mode* (acl2::gag-mode))

;; Keep track of whether or not we're in quiet mode already
(define-var *quiet-mode-state* nil)

(define-var *quiet-mode-on-hooks*
  `((:gag-mode .
     ,(lambda ()
        (setf *saved-gag-mode* (acl2::@ acl2::gag-mode))
        '((acl2::set-gag-mode t))))
    (:inhibit-output-list .
     ,(lambda ()
        (setf *saved-inhibit-output-list* (acl2::@ acl2::inhibit-output-lst))
        '((acl2::set-inhibit-output-lst acl2::*valid-output-names*)))))
  "An alist from symbols (names) to functions that will be called when
  quiet mode is transitioning from disabled to enabled. Each function
  should return a list of ACL2 commands that will be run in addition
  to those any other commands return to enable quiet mode
  behavior. Names are used to refer to particular functions in the
  hook list.")

(defun add-quiet-mode-on-hook (name hook)
  (let ((existing-entry (assoc name *quiet-mode-on-hooks*)))
    (if existing-entry
        (setf (cdr existing-entry) hook)
      (push (cons name hook) *quiet-mode-on-hooks*))))

(defun add-quiet-mode-off-hook (name hook)
  (let ((existing-entry (assoc name *quiet-mode-off-hooks*)))
    (if existing-entry
        (setf (cdr existing-entry) hook)
      (push (cons name hook) *quiet-mode-off-hooks*))))

(define-var *quiet-mode-off-hooks*
  `((:gag-mode .
     ,(lambda ()
       `((acl2::set-gag-mode ,*saved-gag-mode*))))
    (:inhibit-output-list .
     ,(lambda ()
       `((acl2::set-inhibit-output-lst ',*saved-inhibit-output-list*)))))
  "An alist from symbols (names) to functions that will be called when
  quiet mode is transitioning from enabled to disabled. Each function
  should return a list of ACL2 commands that will be run in addition
  to those any other commands return to disable quiet mode behavior,
  ideally reverting to whatever ACL2 settings were in place when quiet
  mode was last enabled. Names are used to refer to particular
  functions in the hook list.")

(defun quiet-mode-on ()
    "Enable quiet mode, turning off as much ACL2 output as possible."
  (unless *quiet-mode-state*
    (let ((state acl2::*the-live-state*)
          (hook-commands
           (loop for (name . hook) in *quiet-mode-on-hooks*
                 append (funcall hook))))
      (setf *disable-comment-window-printing* t)
      (ld-options hook-commands LD-REALLY-QUIET-FLAGS)
      (setf *quiet-mode-state* t))))

#|
 Disable quiet mode, trying to restore settings to as close as
 possible reflect the state prior to quiet-mode-on (if it was called
 previously), or defaults otherwise
|#
(defun quiet-mode-off ()
  (when *quiet-mode-state*
    (let ((state acl2::*the-live-state*)
          (hook-commands
           (loop for (name . hook) in *quiet-mode-off-hooks*
                 append (funcall hook))))
      (ld-options hook-commands LD-REALLY-QUIET-FLAGS)
      (setf *disable-comment-window-printing* nil)
      (setf *quiet-mode-state* nil))))

(defun set-quiet-mode (val)
  (if val (quiet-mode-on) (quiet-mode-off)))

(xdoc::defxdoc-raw acl2s-interface
  :parents (interfacing-tools)
  :short "An interface for interacting with ACL2 from Common Lisp."
  :long " <p>WARNING: Loading this book by default will result in the
redefinition of @('comment-window-co'). This is unfortunately the only
way we found to control comment-window printing. If you would like to
disable this feature, you can add the
@('ACL2S-INTERFACE-NO-OVERWRITE') feature, e.g. by running @('(push
:ACL2S-INTERFACE-NO-OVERWRITE *features*)') in raw mode before
certifying this book.</p>")

(xdoc::defxdoc-raw quiet-mode
  :parents (acl2s-interface)
  :short "Control whether or not the acl2s-interface attempts to suppress ACL2 printed output"
  :long "
Examples:
@({
 (quiet-mode-on)    ; from this point forward all acl2s-interface functions will
                    ; attempt to suppress all ACL2 printed output
 (quiet-mode-off)   ; (default) from this point forward all acl2s-interface
                    ; functions will print any ACL2 output as normal
})
<p>
Most of the ACL2s interface functions also take a @(':quiet') argument for
locally controlling quiet mode without affecting the global setting.
</p>
")

(xdoc::defxdoc-raw capture-output
  :parents (acl2s-interface)
  :short "Control whether or not the acl2s-interface attempts to capture ACL2 printed output"
  :long "
Examples:
@({
 (capture-output-on)    ; From this point forward all acl2s-interface functions will
                        ; attempt to capture all ACL2 printed output
 (capture-output-off)   ; (default) From this point forward all acl2s-interface
                        ; functions will print any ACL2 output as normal
 (get-captured-output)  ; Returns a string containing all captured output since the
                        ; last (get-captured-output) call. Note that the three primary
                        ; acl2s-interface functions will call this before each query.
})
<p>
Most of the ACL2s interface functions also take a @(':capture-output') argument for
locally controlling whether output is captured without affecting the global setting.
</p>
")

(xdoc::defxdoc-raw acl2s-interface-symbol-package-tips
  :parents (acl2s-interface)
  :short "Tips for dealing with symbol package issues when using the ACL2s interface"
  :long "
<p>When using any of the ACL2s interface functions from inside of a package other than \"ACL2\", you may run into problems because the symbols inside of any query literals will default to being interned in that package. This is mainly problematic when it comes to writing expressoions that call ACL2 functions.
</p>
<p>
The simplest way to solve this problem while still working in a non-ACL2 package is to fully specify the names of all functions inside your queries. For example, one would write <tt>(acl2s-compute '(acl2::expt 2 3))</tt> instead of <tt>(acl2s-compute '(expt 2 3))</tt>.
</p>
<p>
This gets painful when writing queries containing many function calls. In this case, depending on your host Lisp, you may be able to use <a href=\"http://www.sbcl.org/manual/#Extended-Package-Prefix-Syntax\">extended package prefix notation</a>. For example, in SBCL, one could write <tt>(acl2s-compute 'acl2::(expt 2 (expt 2 3)))</tt> instead of <tt>(acl2s-compute '(acl2::expt 2 (acl2::expt 2 3)))</tt>.
</p>

<p>
Note that using extended package prefix notation with a backquoted value will also affect any evaluated subexpressions. The following example shows one way of getting around this, by providing the full name of the argument @('foo::x').</p>
@({
(in-package :foo) ;; assume we've defined a package named foo in Common Lisp
(defun baz-ok-1 (x)
  (acl2s-compute `(acl2::expt 2 (acl2::expt 2 ,x))))
(defun baz-bad (x)
  (acl2s-compute `acl2::(expt 2 (expt 2 ,x)))) ;; ,x here will evaluate acl2::x instead of foo::x.
(defun baz-ok-2 (x)
  (acl2s-compute `acl2::(expt 2 (expt 2 ,foo::x)))) ;; we can just override the default package to fix this
})
")

(defun capture-output-on ()
  (setf *capture-output* t))

(defun capture-output-off ()
  (setf *capture-output* nil))

(defun set-capture-output (val)
  "Enable or disable ACL2 output capture."
  (if val (capture-output-on) (capture-output-off)))

;; Determining the appropriate value to pass as an option to ld for
;; each of :standard-co and :proofs-co is somewhat involved, as it
;; depends on whether the user already provided their own value for
;; the setting, whether quiet-mode is on and whether capture-output is
;; true. Thus, we break out this logic into two functions.

;; TODO (drew): determine how to repeat less code between these two
;; functions

(defun calculate-standard-co (props state)
  (or (get-prop props :standard-co)
      (let ((capture-output (if (member :capture-output props :test #'equal) (get-prop props :capture-output) *capture-output*)))
        (cond ((and *quiet-mode-state* capture-output) *capture-output-channel*)
              (*quiet-mode-state* *empty-output-channel*)
              (capture-output
               (let* ((std-co (acl2::standard-co state))
                      (broadcast-stream (make-broadcast-stream *capture-output-stream* (acl2::get-output-stream-from-channel std-co))))
                 (mk-output-channel broadcast-stream state)))
              (t (acl2::standard-co state))))))

(defun calculate-proofs-co (props state)
  (or (get-prop props :proofs-co)
      (let ((capture-output (if (member :capture-output props :test #'equal) (get-prop props :capture-output) *capture-output*)))
        (cond ((and *quiet-mode-state* capture-output) *capture-output-channel*)
              (*quiet-mode-state* *empty-output-channel*)
              (capture-output
               (let* ((proofs-co (acl2::proofs-co state))
                      (broadcast-stream (make-broadcast-stream *capture-output-stream* (acl2::get-output-stream-from-channel proofs-co))))
                 (mk-output-channel broadcast-stream state)))
              (t (acl2::proofs-co state))))))

;; To access the result of an ACL2 command, we will store it
;; somewhere inside of the ACL2 state so that we can access it later.
(define-constant +COMMAND-RESULT-VAR+ 'acl2s-interface-internal::command-result)

;; Save a value inside the ACL2 state for later use.
(defun save-result (val)
  (ld-options `((acl2::assign ,+COMMAND-RESULT-VAR+ ,val))
	      LD-REALLY-QUIET-FLAGS))

;; Recall the last value we saved inside the ACL2 state.
(defun last-result ()
  (let ((state acl2::*the-live-state*))
    (acl2::f-get-global +COMMAND-RESULT-VAR+ state)))

;; TODO (drew): I forget why we store results instead of directly
;; returning them - this may be a vestige of an older
;; implementation. At a minimum, it would likely be faster and simpler
;; to store the last result in a raw Lisp variable rather than inside
;; the ACL2 state.

#|

 If c is an ACL2s computation such as:

 (+ 1 2)
 (append '(1 2) '(3 4))

 etc.

 then the following form will ask ACL2 to evaluate c and will update
 the ACL2 global result to contain a list whose car is a flag
 indicating whether an error occurred, so nil means no error, and whose
 second element is the result of the computation, if no error occurred.

 The keyword argument 'quiet' will turn off as much ACL2s output as
 possible.

 Note that any additional arguments will be passed to ld. This can be
 used to provide keyword arguments that customize ld's behavior.

Here's an older definition

(defun acl2s-compute (c)
  (let ((state acl2::*the-live-state*))
    (multiple-value-bind (erp val state)
        (ld `((assign acl2s::acl2s-result ,c)))
      (if (equal val :eof)
          (ld `((assign acl2s::acl2s-result (list nil (@ acl2s::acl2s-result)))))
        (ld `((assign acl2s::acl2s-result (list t nil))))))
    (last-result)))

|#

(defun acl2s-compute (c &rest args &key quiet capture-output &allow-other-keys)
  (let ((turned-quiet-mode-on (and quiet (not *quiet-mode-state*))))
    (when turned-quiet-mode-on (quiet-mode-on))
    (get-captured-output) ;; clear captured output
    (let ((state acl2::*the-live-state*))
      (acl2::mv-let (erp val state)
		    (ld-options `((acl2::assign ,+COMMAND-RESULT-VAR+ ,c))
				(append (remove-props args '(:quiet :capture-output :ld-error-action))
                                        `(:standard-co ',(calculate-standard-co args state)
                                          :proofs-co ',(calculate-proofs-co args state)
                                          :ld-error-action :error)
                                        (when *quiet-mode-state* LD-QUIET-FLAGS)))
		    (if (equal val :eof)
			(save-result `(list nil (acl2::@ ,+COMMAND-RESULT-VAR+)))
		      (save-result `(list t nil))))
      (cleanup-streams)
      (when turned-quiet-mode-on (quiet-mode-off))
      (last-result))))

(xdoc::defxdoc-raw acl2s-compute
  :parents (acl2s-interface)
  :short "Run a single-value ACL2 computation from Common Lisp"
  :long "
<b>General form</b>
@({
(acl2s-compute
  form                   ; The form to evaluate. Should return a single value.
  :quiet <bool>          ; Optional. Whether or not to suppress all ACL2 printed output. Defaults to nil.
  :capture-output <bool> ; Optional. Whether or not to capture all ACL2 printed output. Defaults to nil.
  ...)       ;; Any additional arguments will be passed to ld, except for :ld-error-action
=>
(list erp val)
})
<dl>
<dt>Returns</dt>
<dd>@('erp') is @('t') if an error occurred during execution of @('form'), and is @('nil') otherwise.</dd>
<dd>@('val') is the single value that @('form') evaluated to.</dd>
</dl>

<p>
The @('form') argument should be an ACL2 expression that evaluates to a single value. Be careful about symbol packages when using @('acl2s-compute') when inside a different package - you may need to fully specify the name of an ACL2 function when calling it. See @(see acl2s-interface-symbol-package-tips) for more information.
</p>

<p>
When the @(':quiet') option is set to @('t'), @('acl2s-compute') will attempt to suppress all ACL2 printed output during evaluation of @('form'). This temporarily overrides the current @(see quiet-mode).
</p>

<p>
When the @(':capture-output') option is set to @('t'), @('acl2s-compute') will attempt capture all ACL2 printed output during evaluation of @('form'). This temporarily overrides the current @(see capture-output).
</p>

<h4>Examples</h4>

@({(acl2s-compute '(+ 1 2))})
Returns (nil 3)
@({(acl2s-compute '(+ 1 2) :quiet nil :ld-pre-eval-print t)})
Returns (nil 3), does not attempt to suppress any ACL2 printed output, and passes @(':ld-pre-eval-print t') to @(see ld)
@({(acl2s-compute '(append '(1 2) '(3 4)))})
Returns (nil (1 2 3 4))
@({(acl2s-compute '(+ 1 '(1 2)))})
Returns (t nil) and prints out a guard violation error message
@({(acl2s-compute '(mv nil t state))})
")

#|
General form:
@({
 (acl2s-compute form   ; The form to evaluate. Should return a single value.
                :quiet ; nil or t. If t, try to suppress as much ACL2 printed
                       ; output as possible. Default nil. Overrides current
                       ; @(see quiet-mode)
                ...)   ; any additional arguments will be passed to ld
})
|#
#|

Here are some examples

(acl2s-compute '(+ 1 2))                   
(acl2s-compute '(+ 1 2) :ld-pre-eval-print t :ld-post-eval-print t)
(acl2s-compute '(append '(1 2) '(3 4)))
(acl2s-compute '(+ 1  '(1 2)))

|#


#|

 If q is acl2s query that returns an error-triple such as 

 (pbt 0)
 (test? (equal x x))
 (thm (equal x x))

 etc.

 then the following form will ask ACL2 to evaluate q and will update
 the ACL2 global result to contain a list whose car is a flag
 indicating whether an error occurred, so nil means no error, and whose
 second element is nil.

 The prover-step-limit is set to ACL2's default value, which may need
 to be updated, based on the application. This can be done either by
 changing the ACL2 default prover step limit (see @(see
 with-prover-step-limit)), or by providing the prover-step-limit
 keyword argument, for example:
 (acl2s-query '(thm (implies (and (natp x) (natp y)) 
                             (>= (+ (abs x) (abs y)) (abs (+ x y))))) 
              :prover-step-limit 10)

 The above query should return (t nil), indicating that the proof
 failed due to the prover exceeding the step limit. Removing the
 :prover-step-limit argument allows the proof to go through.

 The keyword argument 'quiet' will turn off as much ACL2s output as
 possible.

 Note that any additional arguments will be passed to ld. This can be
 used to provide keyword arguments that customize ld's behavior.

 Here is a previous version of the function.

(defun acl2s-query (q)
  (let ((state acl2::*the-live-state*))
    (ld `((mv-let
           (erp val state)
           ,q
           (assign result (list erp nil)))))
    (last-result)))

|#

;; TODO add better error handling. In particular, the current code may return whatever the value of acl2s-result was before this call to acl2s-query
;; TODO I (Drew) changed set-prover-step-limit to with-prover-step-limit to ensure that we don't trample any existing prover-step-limit. Probably faster too. (should benchmark)
(defun acl2s-query (q &rest args &key quiet capture-output (prover-step-limit (get-prover-step-limit)) &allow-other-keys)
  (let ((turned-quiet-mode-on (and quiet (not *quiet-mode-state*))))
    (when turned-quiet-mode-on (quiet-mode-on))
    (get-captured-output) ;; clear captured output
    (let ((state acl2::*the-live-state*))
      (ld-options `((acl2::with-prover-step-limit
                     ,prover-step-limit
		     (acl2::mv-let
		      (erp val acl2::state)
		      ,q
		      (acl2::assign ,+COMMAND-RESULT-VAR+ (list erp val)))))
		  (append (remove-props args '(:quiet :capture-output :prover-step-limit :standard-co :proofs-co :ld-error-action))
                          `(:standard-co ',(calculate-standard-co args state)
                            :proofs-co ',(calculate-proofs-co args state)
                            :ld-error-action :error)
			  (when *quiet-mode-state* LD-QUIET-FLAGS)))
      (cleanup-streams)
      (when turned-quiet-mode-on (quiet-mode-off))
      (last-result))))

(xdoc::defxdoc-raw acl2s-query
  :parents (acl2s-interface)
  :short "Run a multiple-value ACL2 computation from Common Lisp"
  :long "
<b>General form</b>
@({
(acl2s-query
  form                         ; The form to evaluate. Should evaluate to an error triple.
  :quiet <bool>                ; Optional. Whether or not to suppress all ACL2 printed output. Defaults to nil.
  :capture-output <bool>       ; Optional. Whether or not to capture all ACL2 printed output. Defaults to nil.
  :prover-step-limit <integer> ; Optional. Sets the prover step limit. Defaults to what ACL2 would have used
                               ;           for a top-level evaluation (see set-prover-step-limit).
  ...)                         ; Any additional arguments will be passed to ld, except for :ld-error-action
=>
(list erp val)
})
<dl>
<dt>Returns</dt>
<dd>@('erp') is the first value of the error triple that @('form') evaluated to, or @('nil') if an error occurred while evaluating @('form').</dd>
<dd>@('val') is the second value of the error triple that @('form') evaluated to.</dd>
</dl>

<p>
The @('form') argument should be an ACL2 expression that evaluates to an @(see error-triple). @('form') should also not change the state of the ACL2 world with respect to events. Be careful about symbol packages when using @('acl2s-query') when inside a different package - you may need to fully specify the name of an ACL2 function when calling it. See @(see acl2s-interface-symbol-package-tips) for more information.
</p>

<p>
When the @(':quiet') option is set to @('t'), @('acl2s-query') will attempt to suppress all ACL2 printed output during evaluation of @('form'). This temporarily overrides the current @(see quiet-mode).
</p>

<p>
When the @(':capture-output') option is set to @('t'), @('acl2s-query') will attempt capture all ACL2 printed output during evaluation of @('form'). This temporarily overrides the current @(see capture-output).
</p>

<p>
@('acl2s-query') evaluates @('form') inside of a @(see with-prover-step-limit), where the step-limit is set to the value provided to @(':prover-step-limit'), or ACL2's set prover-step-limit if that option is not provided. See @(see set-prover-step-limit) for more information about the prover step-limit. If you don't want to limit the number of prover steps permitted for an event, set @(':prover-step-limit') to nil.
</p>

<h4>Examples</h4>
@({(acl2s-query '(value (+ 1 2)))})
Returns (nil 3)

@({(acl2s-query '(thm (implies (natp x) (integerp x))))})
Returns (nil :invisible)

@({(acl2s-query '(mv nil t state))})
Returns (nil t)

@({(acl2s-query '(value (+ 1 2)) :quiet nil :ld-pre-eval-print t)})
Returns (nil 3), does not attempt to suppress any ACL2 printed output, and passes @(':ld-pre-eval-print t') to @(see ld)

@({(acl2s-query '(trans-eval '(+ 1 2) 'my-ctx state nil))})
Returns (nil ((nil) . 3)). See @(see trans-eval) for more information
about trans-eval's return value.

@({(acl2s-query '(test? (implies (integerp x) (natp x))))})
Returns (t nil)
")

#|

 Here are some examples you can try to see how acl2s-query works.

 (acl2s-query '(pbt 0))
 (acl2s-query '(pbt 0) :post-eval-print nil)
 (acl2s-query '(pbt 0) :pre-eval-print nil)
 (acl2s-query '(pbt 0) :pre-eval-print nil :post-eval-print nil)
 (acl2s-query '(test? (equal x y)))
 (acl2s-query '(thm (equal x x)))
 (acl2s-query '(thm (iff (implies p q)
                         (or (not p) q))))
 (acl2s-query '(thm (implies (and (natp x) (natp y)) 
                             (>= (+ (abs x) (abs y)) (abs (+ x y))))) 
              :prover-step-limit 10)

|#

#|

 If e is acl2s event such as 

 (definec f (x :int) :int 
    (* x x))

 then the following form will ask ACL2 to process the event and will
 update the ACL2 global result to contain a list whose car is a flag
 indicating whether an error occurred, so nil means no error, and
 whose second element is the value returned (can be ignored).

 The prover-step-limit is set to a default value, which may need to be
 updated, based on the application. See the documentation for
 acl2s-query for more information and examples on how to do this.

 The keyword argument 'quiet' will turn off as much ACL2s output as
 possible.

 Note that any additional arguments will be passed to ld. This can be
 used to provide keyword arguments that customize ld's behavior.

 Here is a previous version of the function.

|#

(defun acl2s-event (e &rest args &key quiet capture-output (prover-step-limit (get-prover-step-limit)) &allow-other-keys)
  (let ((turned-quiet-mode-on (and quiet (not *quiet-mode-state*))))
    (when turned-quiet-mode-on (quiet-mode-on))
    (get-captured-output) ;; clear captured output
    (let ((state acl2::*the-live-state*))
      (acl2::mv-let (erp val state)
	  (ld-options `((acl2::with-prover-step-limit
                         ,prover-step-limit
			 ,e))
		      (append (remove-props args '(:quiet :capture-output :prover-step-limit :ld-error-action))
                              `(:standard-co ',(calculate-standard-co args state)
                                :proofs-co ',(calculate-proofs-co args state)
                                :ld-error-action :error)
			      (when *quiet-mode-state* LD-QUIET-FLAGS)))
          (progn
	    (setf erp (not (equal val :eof)))
            (cleanup-streams)
	    (when turned-quiet-mode-on (quiet-mode-off))
	    (list erp nil))))))

(xdoc::defxdoc-raw acl2s-event
  :parents (acl2s-interface)
  :short "Install an ACL2 event from Common Lisp"
  :long "
<b>General form</b>
@({
(acl2s-event
  form                         ; The form to evaluate. Should return an error triple.
  :quiet <bool>                ; Optional. Whether or not to suppress all ACL2 printed output. Defaults to nil.
  :capture-output <bool>       ; Optional. Whether or not to capture all ACL2 printed output. Defaults to nil.
  :prover-step-limit           ; Optional. Sets the prover step limit. Defaults to what ACL2 would have used
                               ;           for a top-level evaluation (see set-prover-step-limit).
  ...)                         ; Any additional arguments will be passed to ld, except for :ld-error-action.
=>
(list erp nil)
})
<dl>
<dt>Returns</dt>
<dd>@('erp') is `nil` if ld indicates that the form was successfully evaluated.</dd>
</dl>

<p>
The @('form') argument should be an ACL2 expression that evaluates to an @(see error-triple). Be careful about symbol packages when using @('acl2s-event') when inside a different package - you may need to fully specify the name of an ACL2 function when calling it. See @(see acl2s-interface-symbol-package-tips) for more information.
</p>

<p>
When the @(':quiet') option is set to @('t'), @('acl2s-event') will attempt to suppress all ACL2 printed output during evaluation of @('form'). This temporarily overrides the current @(see quiet-mode).
</p>

<p>
When the @(':capture-output') option is set to @('t'), @('acl2s-event') will attempt capture all ACL2 printed output during evaluation of @('form'). This temporarily overrides the current @(see capture-output).
</p>

<p>
@('acl2s-event') evaluates @('form') inside of a @(see with-prover-step-limit), where the step-limit is set to the value provided to @(':prover-step-limit'), or ACL2's set prover-step-limit if that option is not provided. See @(see set-prover-step-limit) for more information about the prover step-limit. If you don't want to limit the number of prover steps permitted for an event, set @(':prover-step-limit') to nil.
</p>

<h4>Examples</h4>
@({(acl2s-event '(definec f (x :int) :int (* x x)))})
Returns (nil nil), and defines the function @('f') in the ACL2 world.

@({(acl2s-event '(definec g (x :int) :int (* 5 x)) :quiet t)})
Returns (nil nil), and defines the function @('g') in the ACL2 world. Tries to suppresses all ACL2 printed output during this process.

@({(acl2s-event '(defthm triangle-inequality
                              (implies (and (natp x) (natp y))
                                       (>= (+ (abs x) (abs y)) (abs (+ x y)))))
              :prover-step-limit 200)})
Returns (t nil), indicating that the @('defthm') did not successfully execute. This is because the @('defthm') was limited to 200 prover steps, and more prover steps than that are required to prove it.

@({(acl2s-event '(defthm triangle-inequality
                              (implies (and (natp x) (natp y))
                                       (>= (+ (abs x) (abs y)) (abs (+ x y)))))
              :prover-step-limit 1000)})
Returns (nil nil), and defines the theorem @('triangle-inequality') in the ACL2 world. It limits the @('defthm') call to 1000 prover steps.
")

#|
 Some examples

 (acl2s-event 'acl2s::(definec f (x :int) :int (* x x)))
 (acl2s-event 'acl2s::(definec g (x :int) :int (* 5 x)) :quiet t)
 (acl2s-event 'acl2s::(defthm triangle-inequality
                              (implies (and (natp x) (natp y))
                                       (>= (+ (abs x) (abs y)) (abs (+ x y)))))
              :prover-step-limit 1000)
 (acl2s-query '(pbt 0))

|#
