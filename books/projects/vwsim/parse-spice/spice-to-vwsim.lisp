
; spice-to-vwsim.lisp              Vivek and a small bit of Warren

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

; (ld "spice-to-vwsim.lisp" :ld-pre-eval-print t)

; This file contains functions that convert a parsed-Spice file into
; content suitable for use by the VWSIM simulator.

(in-package "ACL2")
(include-book "parse-spice")
(include-book "../vw-flat-hdl")
(include-book "../vw-hrchl-hdl")

;; Some events that recognize parse-spice output.

(defun spice-name-p (name)
  ;; (:NAME "NAME")
  (declare (xargs :guard t))
  (and (consp name)
       (equal (car name) :NAME)
       (consp (cdr name))
       (stringp (cadr name))
       (standard-char-listp (coerce (cadr name) 'list))))

(defun spice-name (name)
  "Interns a parse-spice (:NAME NAME) form into an ACL2 symbol"
  (declare (xargs :guard (spice-name-p name)))
  (intern (string-upcase (cadr name)) "ACL2"))

(in-theory (disable spice-name))

(defun spice-names-p (names)
  (declare (xargs :guard t))
  (if (atom names)
      t
    (and (spice-name-p (car names))
         (spice-names-p (cdr names)))))

(defun spice-names (names)
  (declare (xargs :guard (spice-names-p names)))
  (if (atom names)
      nil
    (cons (spice-name (car names))
          (spice-names (cdr names)))))

(in-theory (disable spice-names))

(defun spice-component-p (component)
  ;; parse-spice produces component designator symbols in the keyword
  ;; package.
  (declare (xargs :guard t))
  (and (symbolp component)
       (equal (symbol-package-name component) "KEYWORD")))

(defun spice-component (component)
  "Interns keyword symbols into the ACL2 package."
  (declare (xargs :guard (spice-component-p component)))
  (intern (symbol-name component) "ACL2"))

(in-theory (disable spice-component))

(defun spice-node-p (node)
  ;; (:NODE (:NAME "NAME"))
  (declare (xargs :guard t))
  (and (consp node)
       (equal (car node) :NODE)
       (consp (cdr node))
       (spice-name-p (cadr node))))

(defun spice-node (node)
  "Interns a parse-spice (:NODE (:NAME NAME)) form into a symbol."
  (declare (xargs :guard (spice-node-p node)))
  (spice-name (cadr node)))

(defun spice-+node-p (node)
  ;; (:+NODE (:NAME "NAME"))
  (declare (xargs :guard t))
  (and (consp node)
       (equal (car node) :+NODE)
       (consp (cdr node))
       (spice-name-p (cadr node))))

(defun spice-+node (node)
  "Interns a parse-spice (:+NODE (:NAME NAME)) form into a symbol."
  (declare (xargs :guard (spice-+node-p node)))
  (spice-name (cadr node)))

(in-theory (disable spice-+node))

(defun spice--node-p (node)
  ;; (:-NODE (:NAME "NAME"))
  (declare (xargs :guard t))
  (and (consp node)
       (equal (car node) :-NODE)
       (consp (cdr node))
       (spice-name-p (cadr node))))

(defun spice--node (node)
  "Interns a parse-spice (:-NODE (:NAME NAME)) form into a symbol."
  (declare (xargs :guard (spice--node-p node)))
  (spice-name (cadr node)))

(in-theory (disable spice--node))


;; The next few forms are for transmission line nodes

(defun spice-A+-p (node)
  ;; (:A+ (:NAME "NAME"))
  (declare (xargs :guard t))
  (and (consp node)
       (equal (car node) :A+)
       (consp (cdr node))
       (spice-name-p (cadr node))))

(defun spice-A+ (node)
  "Interns a parse-spice (:A+ (:NAME NAME)) form into a symbol."
  (declare (xargs :guard (spice-A+-p node)))
  (spice-name (cadr node)))

(in-theory (disable spice-A+))

(defun spice-A--p (node)
  ;; (:A- (:NAME "NAME"))
  (declare (xargs :guard t))
  (and (consp node)
       (equal (car node) :A-)
       (consp (cdr node))
       (spice-name-p (cadr node))))

(defun spice-A- (node)
  "Interns a parse-spice (:A- (:NAME NAME)) form into a symbol."
  (declare (xargs :guard (spice-A--p node)))
  (spice-name (cadr node)))

(in-theory (disable spice-A--p))

(defun spice-B+-p (node)
  ;; (:B+ (:NAME "NAME"))
  (declare (xargs :guard t))
  (and (consp node)
       (equal (car node) :B+)
       (consp (cdr node))
       (spice-name-p (cadr node))))

(defun spice-B+ (node)
  "Interns a parse-spice (:B+ (:NAME NAME)) form into a symbol."
  (declare (xargs :guard (spice-B+-p node)))
  (spice-name (cadr node)))

(in-theory (disable spice-B+))

(defun spice-B--p (node)
  ;; (:B- (:NAME "NAME"))
  (declare (xargs :guard t))
  (and (consp node)
       (equal (car node) :B-)
       (consp (cdr node))
       (spice-name-p (cadr node))))

(defun spice-B- (node)
  "Interns a parse-spice (:B- (:NAME NAME)) form into a symbol."
  (declare (xargs :guard (spice-B--p node)))
  (spice-name (cadr node)))

(in-theory (disable spice-B-))

(defun spice-nodes-p (nodes)
;; A list of spice-node-p forms
  (declare (xargs :guard t))
  (if (atom nodes)
      t
    (and (spice-node-p (car nodes))
         (spice-nodes-p (cdr nodes)))))

(defun spice-nodes (nodes)
  (declare (xargs :guard (spice-nodes-p nodes)))
  (if (atom nodes)
      nil
    (cons (spice-node (car nodes))
          (spice-nodes (cdr nodes)))))

(defthm symbol-listp-spice-nodes
  (symbol-listp (spice-nodes nodes)))

(in-theory (disable spice-nodes))

(defun spice-branch-p (branch)
  ;; (:NAME "NAME")
  (declare (xargs :guard t))
  (spice-name-p branch))

(defun spice-branch (branch)
  ;; Should we use the occurrence name for the first branch name?  The
  ;; only primitive device so far with more than one branch (which has
  ;; two branches) is the transmission line.
  (declare (xargs :guard (spice-branch-p branch)))
  (spice-name branch))

(in-theory (disable spice-branch))

(defthm characterp-car-string-upcase1
  (implies (and (standard-char-listp l)
                (< 0 (len (string-upcase1 l))))
           (characterp (car (string-upcase1 l)))))

(defun extract-prefix-str (prefix-str)
  "Extracts the unit prefixes; e.g., 'pH' -> 'p'."
  (declare (xargs :guard (and (stringp prefix-str)
                              (standard-char-listp (coerce prefix-str 'list)))))
  (let* ((prefix-str (string-upcase prefix-str)))
    (if (< 1 (length prefix-str))
        ;; ``MEG'' is the only prefix that is longer than 1 character.
        (if (and (< 2 (length prefix-str))
                 (equal (char prefix-str 0) #\M)
                 (equal (char prefix-str 1) #\E)
                 (equal (char prefix-str 2) #\G))
            "MEG"
          ;; if units (e.g. V (Volts), A (Amps), H (Henries)) were
          ;; provided, remove them.
          (string (char prefix-str 0)))
      prefix-str)))

(defconst *limits-alist*
  ;; Translates SPICE prefixes to VWSIM prefixes
  (pairlis$
   '("T" "G" "MEG" "X" "K" "M" "U" "N" "P" "F")
   (list *tera* *giga* *mega* *mega* *kilo* *milli* *micro* *nano* *pico* *femto*)))

(defun spice-number-p (number-list)
  ;; (:NUMBER NUMBER "PREFIX-UNIT")
  (declare (xargs :guard t))
  (and (consp number-list)
       (equal (car number-list) :NUMBER)
       (consp (cdr number-list))
       (rationalp (cadr number-list))
       (consp (cddr number-list))
       ;; The prefix and units is either one string or nil
       (or (null (caddr number-list))
           (and (stringp (caddr number-list))
                (standard-char-listp (coerce (caddr number-list) 'list))))))

(defun spice-number (number-list)
  "Converts a parse-spice (:NUMBER NUMBER UNIT) form into a
   VW-EVAL-TERMP expression."
  (declare (xargs :guard (spice-number-p number-list)))
  (let* ((number (cadr number-list))
         ;; extract prefix from units
         (prefix (and (caddr number-list)
                      (extract-prefix-str (caddr number-list))))
         (prefix-mult (cdr (assoc-equal prefix *limits-alist*)))
         (scale (if prefix-mult prefix-mult 1)))
    (list 'quote (* number scale))))

(defthm vw-eval-termp-spice-number
  (implies (spice-number-p number-list)
           (vw-eval-termp (spice-number number-list))))

(in-theory (disable spice-number))

(defun spice-value-p (value)
  ;; (:VALUE (:NUMBER NUMBER "UNIT"))
  (declare (xargs :guard t))
  (and (consp value)
       (equal (car value) :VALUE)
       (consp (cdr value))
       (spice-number-p (cadr value))))

(defun spice-value (value)
  "Converts a parse-spice (:VALUE (:NUMBER NUMBER UNIT)) form
   into a VW-EVAL-TERMP expression."
  (declare (xargs :guard (spice-value-p value)))
  (let ((number-list (cadr value)))
    (spice-number number-list)))

(defthm vw-eval-termp-spice-value
  (implies (spice-value-p value)
           (vw-eval-termp (spice-value value))))

(in-theory (disable spice-value))

(defun spice-expr-p (expr)
  ;; (:EXPR (:VALUE (:NUMBER NUMBER "UNIT")))
  (declare (xargs :guard t))
  (and (consp expr)
       (equal (car expr) :EXPR)
       (consp (cdr expr))
       (spice-value-p (cadr expr))))

(defun spice-expr (expr)
  "Converts a parse-spice (:EXPR (:VALUE (:NUMBER NUMBER UNIT)))
   form into a VW-EVAL-TERMP expression."
  (declare (xargs :guard (spice-expr-p expr)))
  (spice-value (cadr expr)))

(defthm vw-eval-termp-spice-expr
  (implies (spice-expr-p expr)
           (vw-eval-termp (spice-expr expr))))

(in-theory (disable spice-expr))

(defun spice-values-p (values)
  (declare (xargs :guard t))
  (if (atom values)
      t
    (and (spice-value-p (car values))
         (spice-values-p (cdr values)))))

(defun spice-values (values)
  "Converts a list of parse-spice :VALUE forms into a
   VW-EVAL-TERM-LISTP expression."
  (declare (xargs :guard (spice-values-p values)))
  (if (atom values)
      nil
    (cons (spice-value (car values))
          (spice-values (cdr values)))))

(defthm vw-eval-term-listp-spice-values
  (implies (spice-values-p value)
           (vw-eval-term-listp (spice-values value))))

(in-theory (disable spice-values))

(defun spice-type-p (type)
  ;; (:TYPE TYPE)
  (declare (xargs :guard t))
  (and (consp type)
       (equal (car type) :TYPE)
       (consp (cdr type))
       (stringp (cadr type))
       (standard-char-listp (coerce (cadr type) 'list))))

(defun spice-type (type)
  "Interns a parse-spice (:TYPE TYPE) form) into a symbol."
  (declare (xargs :guard (spice-type-p type)))
  (intern (string-upcase (cadr type)) "ACL2"))

(in-theory (disable spice-type))

(defun spice-io-node-p (node)
  ;; (:IO-NODE "NAME")
  (declare (xargs :guard t))
  (and (consp node)
       (equal (car node) :IO-NODE)
       (consp (cdr node))
       (stringp (cadr node))
       (standard-char-listp (coerce (cadr node) 'list))))

(defun spice-io-node (node)
  "Interns a parse-spice (:IO-NODE NAME) form into an ACL2 symbol"
  (declare (xargs :guard (spice-io-node-p node)))
  (intern (string-upcase (cadr node)) "ACL2"))

(in-theory (disable spice-io-node))

(defun spice-io-nodes-p (nodes)
  (declare (xargs :guard t))
  (if (atom nodes)
      t
    (and (spice-io-node-p (car nodes))
         (spice-io-nodes-p (cdr nodes)))))

(defun spice-io-nodes (nodes)
  (declare (xargs :guard (spice-io-nodes-p nodes)))
  (if (atom nodes)
      nil
      (cons (spice-io-node (car nodes))
            (spice-io-nodes (cdr nodes)))))

(defthm symbol-listp-spice-io-nodes
  (implies (spice-io-nodes-p nodes)
           (symbol-listp (spice-io-nodes nodes))))

(in-theory (disable spice-io-nodes))

(defun spice-param-p (param)
  ;; (:EQUAL (:NAME NAME) (:EXPR (:VALUE (:NUMBER NUMBER PREFIX-UNIT))))
  (declare (xargs :guard t))
  (and (consp param)
       (equal (car param) :EQUAL)
       (consp (cdr param))
       (spice-name-p (cadr param))
       (consp (cddr param))
       (spice-expr-p (caddr param))))

(defun spice-params-p (params)
  (declare (xargs :guard t))
  (if (atom params)
      t
    (and (spice-param-p (car params))
         (spice-params-p (cdr params)))))

(defun spice-b-area-param-p (param)
  "Recognizes a parse-spice JJ's area parameter"
  ;; (:EQUAL (:NAME "area") (:EXPR (:VALUE (:NUMBER NUMBER UNITS))))
  (declare (xargs :guard t))
  (and (spice-param-p param)
       (equal (spice-name (cadr param)) 'area)))

(defun true-list-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let ((key-val (car alist)))
      (and (consp key-val)
           (true-listp key-val)
           (true-list-alistp (cdr alist))))))

(defthm true-list-alistp-forward-to-alistp
  (implies (true-list-alistp alist)
           (alistp alist))
  :rule-classes :forward-chaining)

(defthm true-listp-cdr-assoc-equal-true-list-alistp
  (implies (true-list-alistp alist)
           (true-listp (cdr (assoc-equal key alist)))))

(defun vwsim-param-pos (component param-name)
  "Determines the position of the specified primitive component's
   parameter(s) in *PRIMITIVE-DATABASE*."
  (declare (xargs :guard (and (symbolp component)
                              (symbolp param-name))))
  (let* ((param-names (cadddr (assoc-equal component *primitive-database*)))
         (update-pos (position-equal param-name param-names)))
    update-pos))

(defun spice-model
    (model-name  ;; the key to search up in models alist
     component   ;; the device component type
     parameters  ;; extra parameters not specified in the model
     models      ;; alist of pre-processed models
     )
  "Finds model-name in the list of translated models and modifies it
   using the parameters input."
  ;; Update this definition for other devices' model statements, if
  ;; needed.
  (declare (xargs :guard (and (symbolp model-name)
                              (symbolp component)
                              (true-list-alistp models)
                              (consp parameters)
                              (if (equal component 'B)
                                  (spice-b-area-param-p (car parameters))
                                t))))
  (let ((res (cdr (assoc-equal model-name models))))
    (if (equal component 'B)
        (let ((area-pos (vwsim-param-pos 'B 'area)))
          (if (and parameters area-pos)
              ;; Extract area
              (let ((area (spice-expr (caddr (car parameters)))))
                (update-nth area-pos area res))
            ;; JJs have a default area of 1
            (update-nth area-pos ''1 res)))
          res)))

(defconst *new-branch-str*
  "%")

(defun new-branch (sym)
  "Create a new branch name for devices with more than one branch."
  ;; Generate a branch name for devices with more than one terminal
  ;; (ex. transmission line). We generate a unique name for the branch
  ;; by preppending *new-branch-str* , a reserved character in VWSIM,
  ;; to the name of the device.
  (declare (xargs :guard (symbolp sym)))
  (let* ((str (symbol-name sym))
         (dp-str (string-append *new-branch-str* str))
         (new-symbol (intern dp-str "ACL2")))
      new-symbol))

(defthm vw-eval-termp-car-spice-values
  (implies
   (spice-values-p values)
   (and (vw-eval-termp (car (spice-values values)))
        (vw-eval-termp (cadr (spice-values values)))
        (vw-eval-termp (caddr (spice-values values)))
        (vw-eval-termp (cadddr (spice-values values)))
        (vw-eval-termp (car (cdddr (spice-values values))))
        (vw-eval-termp (car (cddddr (spice-values values))))
        (vw-eval-termp (cadr (cddddr (spice-values values))))))
  :hints
  (("Goal" :in-theory (e/d (spice-values spice-values-p)
                           (member-equal)))))

(defun input-source-values-to-vwsim
    (source-type  ;; PWL, EXP, PULSE, or SIN
     values       ;; a list of spice-values
     time-stop    ;; simulation stop time
     )
  (declare (xargs :guard (and (symbolp source-type)
                              (spice-values-p values)
                              ;; (rational-quotep time-stop)
                              ;; (< 0 (unquote time-stop))
                              )))
  (case source-type
    ('PWL   (b* ((vwsim-pwl-values (spice-values values))
                 ((unless (pwl-expr-okp vwsim-pwl-values))
                  (er hard? 'input-source-values-to-vwsim
                      "SPICE file provides an ill-formed pwl ~
                       waveform: ~p0.~%" vwsim-pwl-values)))
              (f-pwl-src-sym (spice-values values))))
    ('EXP   (b* ((args (spice-values values))
                 (v1 (first args))
                 (v2 (second args))
                 (trise_delay (third args))
                 (trise_delay (if trise_delay trise_delay ''0))
                 (tau_rise (fourth args))
                 (tau_rise (if tau_rise tau_rise '$hn$))
                 (tfall_delay (fifth args))
                 (tfall_delay (if tfall_delay tfall_delay
                                `(f+ ,trise_delay $hn$)))
                 (tau_fall (sixth args))
                 (tau_fall (if tau_fall tau_fall '$hn$))

                 ((unless (and (rational-quotep v1)
                               (rational-quotep v2)
                               (rational-quotep trise_delay)
                               (<= 0 (unquote trise_delay))
                               (rational-quotep tau_rise)
                               (< 0 (unquote tau_rise))
                               (rational-quotep tfall_delay)
                               (< 0 (unquote tfall_delay))
                               (rational-quotep tau_fall)
                               (< 0 (unquote tau_fall))))
                  (er hard? 'input-source-values-to-vwsim
                      "SPICE file provides an ill-formed EXP ~
                       waveform: ~p0.~%" args)))
              (f-exp-src-sym v1 v2 trise_delay tau_rise tfall_delay tau_fall)))
    ('PULSE  (b* ((args (spice-values values))
                  (v1 (first args))
                  (v2 (second args))
                  ;; possibly use default values
                  (tdelay (third args))
                  (tdelay (if tdelay tdelay ''0))
                  (trise (fourth args))
                  (trise (if trise trise '$hn$))
                  (tfall (fifth args))
                  (tfall (if tfall tfall '$hn$))
                  (width (sixth args))
                  (width (if width width '$hn$))
                  (period (seventh args))
                  (period (if period period '$hn$))

                  ((unless (and (rational-quotep v1)
                                (rational-quotep v2)
                                (rational-quotep tdelay)
                                (<= 0 (unquote tdelay))
                                (rational-quotep trise)
                                (< 0 (unquote trise))
                                (rational-quotep tfall)
                                (< 0 (unquote tfall))
                                (rational-quotep width)
                                (< 0 (unquote width))
                                (rational-quotep period)
                                (< 0 (unquote period))
                                (<= (+ (unquote trise) (unquote tfall)
                                       (unquote width))
                                    (unquote period))))
                   (er hard? 'input-source-values-to-vwsim
                       "SPICE file provides an ill-formed PULSE ~
                       waveform: ~ ~p0.~%" args)))
               (f-pulse-src-sym v1 v2 tdelay trise tfall width period)))
    ('SIN    (b* ((args (spice-values values))
                  (voffset (first args))
                  (vpeak (second args))
                  (freq (third args))
                  ((when (and (not freq)
                              (or (not (rational-quotep time-stop))
                                  (not (< 0 (unquote time-stop))))))
                   (er hard? 'input-source-values-to-vwsim
                       "SPICE file provides a SINUSOIDAL input ~
                       source without specifying a frequency. In ~
                       this case, VWSIM demands that the SPICE file
                       provides a non-zero simulation stop time.~%"))
                  (freq (if freq freq (kwote (/ (cadr time-stop)))))
                  (tdelay (fourth args))
                  (tdelay (if tdelay tdelay ''0))
                  (damp_factor (fifth args))
                  (damp_factor (if damp_factor damp_factor ''0))
                  (phase (sixth args))
                  (phase (if phase phase ''0))
                  ((unless (and (rational-quotep voffset)
                                (rational-quotep vpeak)
                                (rational-quotep freq)
                                (<= 0 (unquote freq))
                                (rational-quotep tdelay)
                                (<= 0 (unquote tdelay))
                                ;; damping factor in Hertz
                                (rational-quotep damp_factor)
                                (<= 0 (unquote damp_factor))
                                (rational-quotep phase) ;; phase delay in degrees
                                (<= 0 (unquote phase))))
                   (er hard? 'input-source-values-to-vwsim
                       "SPICE file provides an ill-formed SIN ~
                       waveform: ~ ~p0.~%" args)))
               (f-sin-src-sym voffset vpeak freq tdelay damp_factor phase)))
    (otherwise (er hard?
                   'input-source-values-to-vwsim
                   "unrecognized input source type provided ~p0.~%"
                   source-type))))

(defun spice-subcircuit-name-p (name)
  (declare (xargs :guard t))
  (and (consp name)
       (equal (car name) :SUBCIRCUIT-NAME)
       (consp (cdr name))
       (stringp (cadr name))
       (standard-char-listp (coerce (cadr name) 'list))))

(defun spice-subcircuit-name (name)
  (declare (xargs :guard (spice-subcircuit-name-p name)))
  (intern (string-upcase (cadr name)) "ACL2"))

(defun device-linep (line)
  ;; Recognizer for a parse-spice :DEVICE line.
  (declare (xargs :guard t))
  (and (consp line)
       (consp (car line))
       (equal (caar line) :DEVICE)
       (consp (cdar line))
       (symbolp (cadar line))
       (case-match line
         (((:DEVICE :B) name node+ node- model-name . parameters)
          (and (spice-name-p name)
               (spice-+node-p node+)
               (spice--node-p node-)
               (spice-name-p model-name)
               (consp parameters)
               (spice-b-area-param-p (car parameters))))
         (((:DEVICE :T) name A+ A- B+ B- . parameters)
          (and (spice-name-p name)
               (spice-A+-p A+)
               (spice-A--p A-)
               (spice-B+-p B+)
               (spice-B--p B-)
               (consp parameters)
               (let ((args (car parameters)))
                 (and (consp args)
                      (equal (car args) :LIST)
                      (consp (cdr args))
                      (spice-param-p (cadr args))
                      (consp (cddr args))
                      (spice-param-p (caddr args))))))
         (((:DEVICE :K) name inductor0 inductor1 coupling . &)
          (and (spice-name-p name)
               (spice-name-p inductor0)
               (spice-name-p inductor1)
               (spice-number-p coupling)))
         (((:DEVICE :X) name arg0 arg1 . &)
          (and (spice-name-p name)
               (consp arg0)
               (equal (car arg0) :LIST)
               (spice-nodes-p (cdr arg0))
               (spice-subcircuit-name-p arg1)))
         (((:DEVICE component) name node+ node- . rest)
          (and (spice-component-p component)
               (spice-name-p name)
               (spice-+node-p node+)
               (spice--node-p node-)
               (consp rest)
               (if (member-equal component '(:V :I :P))
                   (and ;; pwl, exp, sin, pulse
                        (spice-name-p (car rest))
                        (consp (cdr rest))
                        ;; list of values
                        (consp (cadr rest))
                        (equal (caadr rest) :LIST)
                        (spice-values-p (cdadr rest)))
                 (spice-value-p (car rest)))))
         (& nil))))

(defun spice-device-to-vwsim (line models time-stop)
  "Converts a :DEVICE line into an VWSIM occurrence"
  (declare (xargs :guard (and (device-linep line)
                              (true-list-alistp models)
                              ;; (rational-quotep time-stop)
                              ;; (< 0 (unquote time-stop))
                              )
                  :guard-hints (("Goal" :in-theory (disable member-equal)))))
  (case-match line
    (((:DEVICE :B) name node+ node- model-name . parameters)
     ;; JJs are specified using models and one optional area parameter
     (list (spice-name name)
           'B
           (list (spice-+node node+) (spice--node node-))
           (list (spice-branch name))
           (spice-model (spice-name model-name) 'B parameters models)))
    (((:DEVICE :T) name A+ A- B+ B- . parameters)
     (list (spice-name name)
           'T
           (list (spice-A+ A+) (spice-A- A-) (spice-B+ B+) (spice-B- B-))
           (let* ((br0 (spice-branch name))
                  (br1 (new-branch br0)))
             (list br0 br1))
           (let* ((args   (car parameters))
                  (values (cdr args))
                  (z0     (spice-expr (caddr (first values))))
                  ;; We assume that the second argument is the time
                  ;; delay. Once we have the equations, we will
                  ;; implement transmission line frequency and normal
                  ;; length
                  (td     (spice-expr (caddr (second values)))))
             (list z0 td)
           )))
    (((:DEVICE :K) name inductor0 inductor1 coupling . &)
     (list (spice-name name)
           'K
           (list (spice-name inductor0) (spice-name inductor1))
           (list (spice-number coupling))))
    (((:DEVICE :X) name arg0 arg1 . &)
     (list (spice-name name)
           (spice-subcircuit-name arg1)
           (spice-nodes (cdr arg0))))

    (((:DEVICE component) name node+ node- . rest)
     (b* ( (spice-name      (spice-name name))
           (spice-component (spice-component component))
           (spice-node+     (spice-+node node+))
           (spice-node-     (spice--node node-))
           (spice-branch    (spice-branch name)))
       ;; split on r,c,l vs v,i,p
       (if (member-equal component '(:V :I :P))
           (b* ((source-type (car rest))
                (values (cadr rest))
                )
             (list spice-name
                   spice-component
                   (list spice-node+ spice-node-)
                   (list spice-branch)
                   (list
                    (let ((source-type-sym (spice-name source-type)))
                      (input-source-values-to-vwsim source-type-sym
                                                    (cdr values)
                                                    time-stop)))))
         (list spice-name
               spice-component
               (list spice-node+ spice-node-)
               (list spice-branch)
               (if (equal (caar rest) :MODEL)
                   ;; Update this to consider models other than JJs!
                   nil
                 (list (spice-value (car rest))))
               ))))
    (& (er hard?
           'spice-device-to-vwsim
           "device and/or arguments are not recognized ~p0.~%"
           line))))

(defun model-linep (line)
  "Recognizes a parse-spice (:STATEMENT :MODEL) line"
  (declare (xargs :guard t))
  (and (consp line)
       (consp (car line))
       (equal (caar line) :STATEMENT)
       (consp (cdar line))
       (equal (cadar line) :MODEL)
       (consp (cdr line))
       (spice-name-p (cadr line))
       (consp (cddr line))
       (spice-type-p (caddr line))
       (consp (cdddr line))
       (consp (cadddr line))
       (equal (car (cadddr line)) :LIST)
       (spice-params-p (cdr (cadddr line)))))

(defun tran-linep (line)
  "Recognizes a parse-spice (:STATEMENT :TRAN) line"
  (declare (xargs :guard t))
  (and (consp line)
       (consp (car line))
       (equal (caar line) :STATEMENT)
       (consp (cdar line))
       (equal (cadar line) :TRAN)
       (consp (cdr line))
       (consp (cadr line))
       (equal (caadr line) :LIST)
       (spice-values-p (cdadr line))))

(defun global-linep (line)
  "Recognizes a parse-spice (:STATEMENT :GLOBAL) line"
  (declare (xargs :guard t))
  (and (consp line)
       (consp (car line))
       (equal (caar line) :STATEMENT)
       (consp (cdar line))
       (equal (cadar line) :GLOBAL)
       (consp (cdr line))
       (consp (cadr line))
       (equal (caadr line) :LIST)
       (spice-nodes-p (cdadr line))))

(defun subckt-linep (line)
  "Recognizes a parse-spice (:STATEMENT :SUBCKT) line"
  (declare (xargs :guard t))
  (and (consp line)
       (consp (car line))
       (equal (caar line) :STATEMENT)
       (consp (cdar line))
       (equal (cadar line) :SUBCKT)
       (consp (cdr line))
       (spice-name-p (cadr line))
       (consp (cddr line))
       (consp (caddr line))
       (equal (caaddr line) :LIST)
       (spice-io-nodes-p (cdaddr line))))

(defun ends-linep (line)
  "Recognizes a parse-spice (:STATEMENT :ENDS) line"
  (declare (xargs :guard t))
  (and (consp line)
       (consp (car line))
       (equal (caar line) :STATEMENT)
       (consp (cdar line))
       (equal (cadar line) :ENDS)
       (if (consp (cdr line))
           (spice-name-p (cadr line))
         t)))

;; JoSIM says the following about output commands:
;; (see https://joeydelp.github.io/JoSIM/syntax/)

;; These output commands can be of either
;; .print .plot .save

;; Any of these commands can be followed by either of the following
;; commands

;; PrintType Device or Node

;; PType(Device or Node)0 ...  PType(Device or Node)n

;; Where PrintType can be either device voltage (DEVV), device current
;; (DEVI), device phase (PHASE), node voltage (NODEV) or node phase
;; (NODEP).

;; When specifying a device type store only a single device can be
;; specified, but when a node type store is specified 2 nodes can be
;; specified to store the difference between them.

;; PType is shorthand for the above and can have multiple per line
;; requests. PType can be either of V, I (or C) or P followed by the
;; device or node in brackets. If more than one device or node is
;; specified by comma seperation (maximum 2) the difference between
;; the two devices or nodes is stored.

(defun print-linep (line)
  "Recognizes a parse-spice (:STATEMENT :PRINT) line"
  (declare (xargs :guard t))
  (case-match line
    (((:STATEMENT :PRINT) type name)
     (and (spice-type-p type)
          (spice-name-p name)))
    (& nil)))

(defun linep (line)
  ;; Recognizer for a parsed line produced by parse-spice.  A
  ;; parse-spice line is one of 3 types -> :COMMENT, :STATEMENT, or
  ;; :DEVICE
  (declare (xargs :guard t))
  (and (consp line)
       (if (equal (car line) :COMMENT)
           t
         ;; (:STATEMENT STATEMENT) or (:DEVICE DEVICE)
         (let ((type (car line)))
           (and
            (consp type)
            (consp (cdr type))
             (case (car type)
               (:STATEMENT
                (case (cadr type)
                  (:MODEL (model-linep line))
                  (:PRINT (print-linep line))
                  (:SUBCKT (subckt-linep line))
                  (:END t)
                  (:ENDS (ends-linep line))
                  (:GLOBAL (global-linep line))
                  (:PARAM t)
                  (:TRAN (tran-linep line))
                  (otherwise nil)))
               (:DEVICE (device-linep line))
               (otherwise nil)))))))

(defun linesp (lines)
  (declare (xargs :guard t))
  (if (atom lines)
      t
    (and (linep (car lines))
         (linesp (cdr lines)))))

(defun er-1 (ctx msg arg)
  (declare (xargs :guard t))
  (er hard? ctx msg arg))

(defun er-2 (ctx msg arg0 arg1)
  (declare (xargs :guard t))
  (er hard? ctx msg arg0 arg1))

(in-theory (disable er-1 er-2))

(defun spice-to-vwsim-help
    (netlist ;; result from parse-spice
     models ;; we pre-process the models
     module-name ;; current module
     module-IOs  ;; current module's IOs
     occs        ;; current module's occurrences list
     modules     ;; list of modules created
     time-stop   ;; simulation stop time
     )
  (declare (xargs :guard (and (linesp netlist)
                              (true-list-alistp models)
                              (symbolp module-name)
                              (symbol-listp module-IOs)
                              (true-listp modules)
                              ;; (rational-quotep time-stop)
                              ;; (< 0 (unquote time-stop))
                              )
                  :hints (("Goal" :in-theory (disable module-syntax-okp
                                                      occ-syntax-okp
                                                      member-equal)))
                  :verify-guards nil
                  :measure (len netlist)))
  (if (atom netlist)
      (mv (cons (list module-name
                      module-IOs
                      occs)
                modules)
          netlist)
    (let* ((parsed-line (car netlist))
           (line-type   (car parsed-line)))
      (if (equal line-type :COMMENT)
          (spice-to-vwsim-help (cdr netlist) models module-name module-IOs
                               occs modules time-stop)
        (let ((line-type (car line-type)))
          (case line-type
            (:STATEMENT
             (let ((statement-type (cadar parsed-line)))
               (case statement-type
                 (:MODEL
                  (spice-to-vwsim-help (cdr netlist) models module-name
                                       module-IOs occs modules time-stop))
                 (:PRINT
                  (spice-to-vwsim-help (cdr netlist) models module-name
                                       module-IOs occs modules time-stop))
                 (:SUBCKT
                  (b* ((new-name (spice-name (cadr parsed-line)))
                       (new-IOs (spice-io-nodes (cdaddr parsed-line)))
                       ((mv subckt-modules rest-netlist)
                        (spice-to-vwsim-help (cdr netlist) models new-name
                                             new-IOs nil nil time-stop)))
                    (spice-to-vwsim-help
                     ;; The mbt check helps with the measure. We prove
                     ;; this ``must be true'' while proving the guards.
                     (if (mbt (< (len rest-netlist)
                                 (len netlist)))
                         rest-netlist
                       (cdr netlist))
                     models
                     module-name
                     module-IOs
                     occs
                     (append modules subckt-modules)
                     time-stop)))
                 (:END
                  (mv (cons (list module-name module-IOs occs) modules)
                           nil))
                 (:ENDS
                  (if (consp (cdr parsed-line))
                      ;; check which subcircuit definition is being ended
                      (if (equal (spice-name (cadr parsed-line)) module-name)
                          (b* ((module (list module-name module-IOs occs))
                               ((unless (module-syntax-okp module))
                                (prog2$ (er-1 'spice-to-vwsim-help
                                              "the subcircuit ~p0 ~
                                               being defined is ~
                                               ill-formed.~%"
                                              module-name)
                                        (mv modules nil))))
                               (mv (cons module modules)
                                   (cdr netlist)))
                        (prog2$
                         (er-2 'spice-to-vwsim-help
                               "The statement,~p0, does not end the ~
                                expected subcircuit definition: ~
                                ~p1.~%"
                               parsed-line module-name)
                         (mv modules nil)))
                    (mv (cons (list module-name module-IOs occs) modules)
                        (cdr netlist))))
                 ;; we extract the global nodes in a separate sweep of
                 ;; the netlist
                 (:GLOBAL
                  (spice-to-vwsim-help (cdr netlist) models module-name
                                       module-IOs occs modules time-stop))
                 (:PARAM
                  (prog2$ (cw "spice-to-vwsim-help: :PARAM being ignored!~%")
                          (spice-to-vwsim-help (cdr netlist) models module-name
                                               module-IOs occs modules
                                               time-stop)))
                 (:TRAN
                  (spice-to-vwsim-help (cdr netlist) models module-name
                                       module-IOs occs modules
                                       time-stop))
                 (otherwise
                  (prog2$
                   (cw "spice-to-vwsim-help: ignoring unrecognized ~
                        STATEMENT type: ~p0.~%" parsed-line)
                   (spice-to-vwsim-help (cdr netlist) models module-name
                                        module-IOs occs modules
                                        time-stop))))))
            (:DEVICE
             (b* ((device (spice-device-to-vwsim
                           parsed-line models time-stop))
                  ((unless (occ-syntax-okp device))
                   (prog2$ (er-1 'spice-to-vwsim-help
                                 "the following device is ~
                                  ill-formed: ~% ~p0~%"
                                 device)
                           (mv modules nil))))
               (spice-to-vwsim-help (cdr netlist) models module-name module-IOs
                                    (cons device occs)
                                    modules time-stop)))
            (otherwise
             (prog2$
              (cw "spice-to-vwsim-help: ignoring line that is not of ~
                   type :COMMENT, :STATEMENT, or :DEVICE.~%" parsed-line)
              (spice-to-vwsim-help (cdr netlist) models module-name
                                   module-IOs occs modules
                                   time-stop)))))))))

(defthm true-listp-car-spice-to-vwsim-help
  (implies (true-listp modules)
           (true-listp
            (CAR
             (SPICE-TO-VWSIM-HELP netlist models module-name
                                  module-IOs occs modules
                                  time-stop))))
  :hints
  (("Goal" :in-theory (disable member-equal module-syntax-okp occ-syntax-okp
                               spice-device-to-vwsim))))

(defthm linesp-mv-nth-1-spice-to-vwsim-help
  (implies (linesp netlist)
           (linesp
            (mv-nth 1
                    (SPICE-TO-VWSIM-HELP netlist models module-name
                                         module-IOs occs modules
                                         time-stop))))
  :hints
  (("Goal" :in-theory (disable member-equal device-linep ends-linep
                               global-linep model-linep tran-linep
                               subckt-linep mv-nth linep
                               module-syntax-okp occ-syntax-okp
                               spice-device-to-vwsim))))

(in-theory (disable spice-to-vwsim-help))

(defthm true-listp-append-2
  (implies (and (true-listp a)
                (true-listp b))
           (true-listp (append a b)))
  :rule-classes :type-prescription)

(defthm true-listp-append-car-spice-to-vwsim-help
  (implies (and (true-listp new-modules)
                (true-listp modules))
           (true-listp
            (append
             new-modules
             (CAR (SPICE-TO-VWSIM-HELP netlist models module-name
                                       module-IOs occs modules
                                       time-stop)))))
  :hints
  (("Goal"
    :use ((:instance
           true-listp-append-2
           (a modules)
           (b (CAR (SPICE-TO-VWSIM-HELP netlist models module-name
                                        module-IOs occs modules
                                        time-stop))))))))

;; prove guards of spice-to-vwsim-help
(encapsulate
  ()

  (defthm len-spice-to-vwsim-help-1
    (if (consp netlist)
        (< (len (mv-nth 1
                        (SPICE-TO-VWSIM-HELP netlist models module-name
                                             module-IOs occs modules
                                             time-stop)))
           (len netlist))
      (=
       (len (mv-nth 1
                    (SPICE-TO-VWSIM-HELP netlist models module-name
                                         module-IOs occs modules
                                         time-stop)))
       (len netlist)))
    :hints
    (("Goal" :in-theory (e/d (spice-to-vwsim-help)
                             (spice-device-to-vwsim)))))

  (defthm len-spice-to-vwsim-help-2
    (implies (consp netlist)
             (<
              (len
               (mv-nth 1
                       (SPICE-TO-VWSIM-HELP (cdr netlist) models module-name
                                            module-IOs occs modules
                                            time-stop)))
              (len netlist)))
    :hints
    (("Goal" :use ((:instance len-spice-to-vwsim-help-1
                              (netlist (cdr netlist)))))))

  (verify-guards spice-to-vwsim-help
    :hints
    (("Goal" :in-theory (disable device-linep global-linep
                                 model-linep
                                 spice-device-to-vwsim)))))

(defun expand-ends-help-1 (parent)
  (declare (xargs :guard t))
  `((:STATEMENT :ENDS) ,parent))

(defthm linep-expand-ends-help-1
  (implies (spice-name-p parent)
           (ends-linep (expand-ends-help-1 parent))))

(defun expand-ends-help (parents)
  "Helper for expand-ends"
  (declare (xargs :guard (true-listp parents)))
  (if (atom parents)
      nil
    (cons (expand-ends-help-1 (car parents))
          (expand-ends-help (cdr parents)))))

(defthm ends-linep-expand-ends-help
  (implies (spice-names-p parents)
           (linesp (expand-ends-help parents))))

(in-theory (disable expand-ends-help))

(defun expand-ends (netlist parents)
  ;; Taken from SPICE3 Version 3f3 User's Manual The "Ends" line must
  ;; be the last one for any subcircuit definition. The subcircuit
  ;; name, if included, indicates which subcircuit definition is being
  ;; terminated; if omitted, all subcircuits being defined are
  ;; terminated. The name is needed only when nested subcircuit
  ;; definitions are being made.
  "Expands the :ENDS statements to specify which subcircuit is being
   ended."
  (declare (xargs :guard (and (linesp netlist)
                              (true-listp parents))
                  :guard-hints
                  (("Goal" :in-theory (disable member-equal
                                               device-linep
                                               global-linep linep)))))
  (if (atom netlist)
      nil
    (let ((line (car netlist)))
      (if (subckt-linep line)
          (cons (car netlist)
                (expand-ends (cdr netlist)
                             (cons (cadr line) parents)))
        (if (ends-linep line)
            (if (consp (cdr line))
                (if (equal (cadr line) (car parents))
                    (cons (car netlist)
                          (expand-ends (cdr netlist)
                                       (cdr parents)))
                  (cw "expand-ends: this line does not end the ~
                      current subcircuit being defined ~p0.~%" line))
              ;; just .ends
              (let ((expanded-ends (expand-ends-help parents)))
                (append expanded-ends
                        (expand-ends (cdr netlist) nil))))
          (cons (car netlist)
                (expand-ends (cdr netlist)
                             parents)))))))

(defthm linesp-append
  (implies (and (linesp l1)
                (linesp l2))
           (linesp (append l1 l2)))
  :hints
  (("Goal" :in-theory (disable member-equal device-linep ends-linep
                               global-linep linep))))

(defthm linesp-expand-ends
  (implies (and (linesp netlist)
                (spice-names-p parents))
           (linesp (expand-ends netlist parents)))
  :hints
  (("Goal" :in-theory (disable member-equal device-linep
                               global-linep tran-linep linep))))

(defconst *model-type-alist*
  ;; Model types allowed in SPICE
  '(("c" . c)
    ("l" . l)
    ("r" . r)
    ;; convention adopted from WRSpice and JoSIM
    ("jj" . b)))

(defun extract-model-help (component arg-list res)
  "Helper for extract-model"
  (declare (xargs :guard (and (symbolp component)
                              (spice-params-p arg-list)
                              (true-listp res))))
  (if (atom arg-list)
      res
    (let* ((arg (car arg-list))
           (arg-name (spice-name (cadr arg)))
           (update-pos (vwsim-param-pos component arg-name))
           (arg-num  (spice-expr (caddr arg))))
      (if update-pos
          (extract-model-help component
                              (cdr arg-list)
                              (update-nth update-pos arg-num res))
        (extract-model-help component
                            (cdr arg-list)
                            res)))))

(defthm true-listp-extract-model-help
  (implies (and (symbolp component)
                (spice-params-p arg-list)
                (true-listp res))
           (true-listp (extract-model-help component arg-list res))))

(in-theory (disable extract-model-help))

(defun extract-model (model-line)
  "Converts a parse-spice (:STATEMENT :MODEL) line a name and
   value-list pair"
  (declare (xargs :guard (model-linep model-line)))
  (let* ((model (cdr model-line))
         (name (spice-name (car model)))
         (component (cdr (assoc-equal (cadr (cadr model)) *model-type-alist*)))
         (arg-list (cdaddr model)))
    (cons name (extract-model-help component arg-list nil))))

(defun extract-models (netlist)
  "Creates an alist of models in the parse-spice netlist. The keys are
   the model names and the values are the list of parameters specified
   in the model statement, placed in the order VWSIM recognizes."
  (declare (xargs :guard (linesp netlist)))
  (if (atom netlist)
      nil
    (let* ((line (car netlist)))
      (if (model-linep line)
          (cons (extract-model line)
                (extract-models (cdr netlist)))
        (extract-models (cdr netlist))))))

(defthm true-list-alistp-extract-models
  (implies (linesp netlist)
           (true-list-alistp (extract-models netlist)))
  :hints
  (("Goal" :in-theory (disable linep device-linep))))

(defun extract-tran (netlist)
  ;; .TRAN TSTEP TSTOP <TSTART <TMAX>>
  ;; we expect TSTEP,TSOP,TSTART,TMAX to be rational numbers
  (declare (xargs :guard (linesp netlist)))
  (if (atom netlist)
      nil
    (let* ((line (car netlist)))
      (if (tran-linep line)
          ;; extract simulation start, step-size, end
          (let* ((values (cdadr line))
                 (spice-values (spice-values values)))
            spice-values)
        (extract-tran (cdr netlist))))))

(defthm vw-eval-term-listp-extract-tran
  (implies (linesp netlist)
           (and (vw-eval-termp (car (extract-tran netlist)))
                (vw-eval-termp (cadr (extract-tran netlist)))
                (vw-eval-termp (caddr (extract-tran netlist)))
                (vw-eval-termp (cadddr (extract-tran netlist)))))
  :hints
  (("Goal" :in-theory (disable member-equal device-linep linep))))

(in-theory (disable extract-tran))

(defun extract-globals (netlist)
  ;; .GLOBAL NODE
  ;; taken from WRSpice manual
  ;; The arguments are node names. These declared node names remain
  ;; unaltered when subcircuits are expanded, thus the indicated nodes
  ;; become accessible throughout the circuit.
  (declare (xargs :guard (linesp netlist)))
  (if (atom netlist)
      nil
    (let* ((line (car netlist)))
      (if (global-linep line)
          ;; extract simulation start, step-size, end
          (append (spice-nodes (cdadr line))
                  (extract-globals (cdr netlist)))
        (extract-globals (cdr netlist))))))

(defthm cdr-standard-char-listp
  (implies (standard-char-listp l)
           (standard-char-listp (cdr l)))
  :hints
  (("Goal" :in-theory (enable standard-char-listp))))

(defun format-print-name-help (print-name-list old-concat-char new-concat-char)
  (declare (xargs :guard (standard-char-listp print-name-list)))
  (if (atom print-name-list)
      nil
    (let* ((char (car print-name-list))
           (new-char (if (equal char old-concat-char)
                         new-concat-char
                       char)))
      (cons new-char (format-print-name-help (cdr print-name-list)
                                             old-concat-char new-concat-char)))))

(defthm standard-char-listp-format-print-name-help
  (implies (and (standard-char-listp print-name-list)
                (standard-char-p char1)
                (standard-char-p char2))
           (standard-char-listp
            (format-print-name-help print-name-list char1 char2)))
  :hints
  (("Goal" :in-theory (enable standard-char-listp))))

(in-theory (disable standard-char-listp))

(defun format-print-name (print-name old-concat-char new-concat-char)
  (declare (xargs :guard (and (characterp old-concat-char)
                              (standard-char-p old-concat-char)
                              (characterp new-concat-char)
                              (standard-char-p new-concat-char)
                              (stringp print-name)
                              (standard-char-listp (coerce print-name 'list)))))
  (coerce (format-print-name-help (coerce print-name 'list)
                                  old-concat-char
                                  new-concat-char)
          'string))

(encapsulate
  ()
  (defthm standard-char-listp-coerce-coerce
    (implies (standard-char-listp l)
             (standard-char-listp (coerce (coerce l 'string)
                                          'list)))
    :hints
    (("Goal" :in-theory (enable standard-char-listp))))

  (defthm standard-char-listp-coerce-format-print-name
    (implies (and (standard-char-p old-concat-char)
                  (standard-char-p new-concat-char)
                  (standard-char-listp (coerce print-name 'list)))
             (standard-char-listp
              (coerce (format-print-name print-name old-concat-char
                                         new-concat-char)
                      'list)))
    :hints
    (("Goal" :in-theory (enable standard-char-listp)))))

(in-theory (disable format-print-name))

(defun extract-prints (netlist old-concat-char vw-concat-char)
  ;; JoSIM format-> ((:STATEMENT :PRINT) (:TYPE type) (:NAME name))
  (declare (xargs :guard (and (linesp netlist)
                              (characterp old-concat-char)
                              (standard-char-p old-concat-char)
                              (characterp vw-concat-char)
                              (standard-char-p vw-concat-char))))
  (if (atom netlist)
      nil
    (let ((line (car netlist)))
      (if (print-linep line)
          (let* ((params (cdr line))
                 (name-str (cadr (cadr params)))
                 ;; normally we would use the function spice-name, BUT
                 ;; we would like to replace the concatenation
                 ;; character with our representation of concatenation
                 ;; with the #\/ character.  Ex. "BJI|J3|XLATCH" =
                 ;; "BJI/J3/XLATCH".
                 (new-name (format-print-name name-str old-concat-char
                                              vw-concat-char))
                 (new-name-sym (intern (string-upcase new-name) "ACL2")))
            (cons (cons (spice-type (car params))
                        new-name-sym)
                  (extract-prints (cdr netlist) old-concat-char
                                  vw-concat-char)))
        (extract-prints (cdr netlist) old-concat-char vw-concat-char)))))

(defun spice-to-vwsim (netlist cir-concat-char vw-concat-char)
  "Converts the output of the parse-spice function into a VWSIM
  heirarchical netlist representation"
  ;; taken from SPICE3 Version 3f3 User's Manual
  ;; TSTEP is the printing or plotting increment for line-printer
  ;; output. For use with the post-processor, TSTEP is the suggested
  ;; computing increment. TSTOP is the final time, and TSTART is the
  ;; initial time. If TSTART is omitted, it is assumed to be zero. The
  ;; transient analysis always begins at time zero. In the interval
  ;; <zero, TSTART>, the circuit is analyzed (to reach a steady state),
  ;; but no outputs are stored. In the interval <TSTART, TSTOP>, the
  ;; circuit is analyzed and outputs are stored. TMAX is the maximum
  ;; step- size that SPICE uses; for default, the program chooses either
  ;; TSTEP or (TSTOP-TSTART)/50.0, which- ever is smaller. TMAX is
  ;; useful when one wishes to guarantee a computing interval which is
  ;; smaller than the printer increment, TSTEP.
  (declare (xargs :guard (and (linesp netlist)
                              (characterp cir-concat-char)
                              (standard-char-p cir-concat-char)
                              (characterp vw-concat-char)
                              (standard-char-p vw-concat-char))))
  (b* ((models (extract-models netlist))
       (globals (extract-globals netlist))
       (times  (extract-tran netlist))
       (prints (extract-prints netlist cir-concat-char vw-concat-char))
       (time-step (first times))
       (time-stop (second times))
       (time-start (third times))
       (time-start (if time-start
                       time-start
                     ''0))
       #||
       ((unless (and (rational-quotep time-stop)
                     (< 0 (unquote time-stop))))
        (er hard? 'spice-to-vwsim
            "SPICE file provides a simulation stop time that is not ~
            rational.~%"))
       ||#
       ;; we don't currently use time-step-max. If needed, perform the
       ;; calculation for the max time step size at the top-level, as
       ;; the time-step, time-stop, and/or time-start may not be
       ;; provided in the SPICE file.
       #||
       (time-step-max (fourth times))
       (time-step-max (if time-step-max
                          time-step-max
                        (if (< (cadr time-step)
                               (/ (- (cadr time-stop) (cadr time-start)) 50))
                             time-step
                           (/ (- (cadr time-stop) (cadr time-start)) '50))))
       ||#
       (netlist (expand-ends netlist nil))
       ((mv result ?netlist)
        (spice-to-vwsim-help netlist models 'top nil nil nil
                             time-stop)))
    (list
     (cons :modules result)                ;; heirarchical netlist
     (cons :time-step time-step)           ;; simulation step size
     (cons :time-stop time-stop)           ;; simulation stop time
     (cons :time-start time-start)         ;; simulation start time
; (cons :time-step-max time-step-max)   ;; simulation max step size
     (cons :global-nodes globals)
     (cons :prints prints)
     )))

(defun ps (file state)
  (declare (xargs :guard (and ; (symbolp var)
                              (stringp file))
                  :stobjs state
                  :mode :program))
  (b* (;; Parse the file.
       ((mv ps-er-flg ps-value state)
        (parse-spice-fn file nil state))

       ;; If parse unsuccessful, exit
       ((when ps-er-flg) state))

    (put-global 'ans ps-value state)))

;; The following events are for generating user-readable VWSIM output

(defun gen-output-name
  ;; Returns a string that modifies the VWSIM name for a device back
  ;; to the name originally used in the ".cir" file.
    (name
     type               ;; typically either "V","I", or "P"
     old-concat-char    ;; the character used in the cir file to
                        ;; flatten heirarchical occurrences (Example:
                        ;; #\| in BJi|XJ6|XLATCH)
     vw-concat-char     ;; the character used in vwsim to flatten
                        ;; heirarchical occurrences (Example: #|/ in
                        ;; BJi/XJ6/XLATCH)
     )
  (declare (xargs :guard (and (symbolp name)
                              (stringp type)
                              (standard-char-listp (coerce type 'list))
                              (characterp old-concat-char)
                              (standard-char-p old-concat-char)
                              (characterp vw-concat-char)
                              (standard-char-p vw-concat-char))
                  :guard-hints (("Goal" :in-theory (enable symlp)))))
  (b* ((symbol-name (symbol-name name))
       ((unless (standard-char-listp (coerce symbol-name 'list)))
        (prog2$
         (cw "gen-output-name: the symbol ~p0 is not a string of ~
             standard characters.~%" name)
         ;; we return "NIL" to ensure that this function returns a
         ;; string.
         "NIL"))
       ;; Convert vwsim's heirarchical concatenation character back
       ;; to the concatenation character used in the ".cir" file
       (new-symbol-name (format-print-name symbol-name vw-concat-char
                                           old-concat-char))
       (new-symbol-name (concatenate 'string type "(" new-symbol-name ")"))
       (new-name new-symbol-name))
    new-name))

(defun symbol-symbol-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (let ((entry (car x)))
      (and (consp entry)
           (symbolp (car entry))
           (symbolp (cdr entry))
           (symbol-symbol-alistp (cdr x))))))

(defun gen-output-names (al old-concat-char vw-concat-char)
  (declare (xargs :guard (and (symbol-symbol-alistp al)
                              (characterp old-concat-char)
                              (standard-char-p old-concat-char)
                              (characterp vw-concat-char)
                              (standard-char-p vw-concat-char))))
  ;; al contains the simulation output requests. Example: '((DEVV
  ;; . singal0) (DEVI . signal1) ...). This function produces a string
  ;; for each request in al, which will be the new key in the output
  ;; (ex. csv file or alist).
  (if (atom al)
      nil
    (let* ((pair (car al))
           (type (car pair))
           (name (cdr pair)))
      (let ((new-name
             (case type
               ((NODEV DEVV)
                (gen-output-name name "V" old-concat-char vw-concat-char))
               ((NODEP PHASE)
                (gen-output-name name "P" old-concat-char vw-concat-char))
               ((DEVI)
                (gen-output-name name "I" old-concat-char vw-concat-char))
               (otherwise ""))))
        (cons new-name
              (gen-output-names (cdr al) old-concat-char vw-concat-char))))))

(defun phase-to-voltage-help (vals constant)
  "Converts a list of phase derivative values to voltage values"
  (declare (xargs :guard (and (rational-listp vals)
                              (rationalp constant))))
  (if (atom vals)
      nil
    (cons (f* constant (car vals))
          (phase-to-voltage-help (cdr vals) constant))))

(defun phase-to-voltage (node records)
  "Converts the phase values of a node to voltage values (with respect
  to ground)."
  ;; This function will primarily be used after a phase-based
  ;; simulation
  (declare (xargs :guard (and (symbolp node)
                              (symbol-rational-list-alistp records))))
  (b* ((dp-node-vals (assoc (dp node) records))
       ((unless (consp dp-node-vals))
        (cw "phase-to-voltage: the node ~p0 does not exist in the ~
            simulation output.~%" node))
       (dp-vals (cdr dp-node-vals))
       (constant (f/ (r2f (f*phi0*))
                     (f* (r2f 2) (r2f (f*pi*))))))
    (phase-to-voltage-help dp-vals constant)))

(defthm rational-listp-phase-to-voltage
  (implies (symbol-rational-list-alistp records)
           (rational-listp (phase-to-voltage node records))))

(in-theory (disable phase-to-voltage))

(defun voltage-to-phase-help (voltages hns prev-voltage prev-phase constant)
  (declare (xargs :guard (and (rational-listp voltages)
                              (rational-listp hns)
                              (rationalp prev-voltage)
                              (rationalp prev-phase)
                              (rationalp constant))))
  (if (or (atom voltages) (atom hns))
      nil
    (b* ((voltage (car voltages))
         (hn (car hns))
         (phase (f+ prev-phase
                    ;; phi_n = phi_n-1 + (hn/2)*(2e/hbar)*(V_n-1 + V_n)
                    (f* (f* (f/ hn (r2f 2)) constant)
                        (f+ prev-voltage voltage)))))
      (cons phase (voltage-to-phase-help (cdr voltages) (cdr hns)
                                         voltage phase constant)))))

(defthm rational-listp-voltage-to-phase-help
  (implies (and (rational-listp voltages)
                (rational-listp hns)
                (rationalp prev-voltage)
                (rationalp prev-phase)
                (rationalp constant))
           (rational-listp (voltage-to-phase-help voltages hns prev-voltage
                                                  prev-phase constant))))

(defun voltage-to-phase (node records)
  "Converts the voltage values of a node to phase values"
  ;; This function will primarily be used after a voltage-based
  ;; simulation
  (declare (xargs :guard (and (symbolp node)
                              (symbol-rational-list-alistp records))))
  ;; we use the formula for the phase guess (see main.pdf) to
  ;; calculate the phase at each time step
  ;; phi_n = phi_n-1 + (hn/2)*(2e/hbar)*(V_n-1 + V_n)
  (b* ((voltages (cdr (assoc node records)))
       (hns (cdr (hons-assoc-equal '$hn$ records)))
       (constant (f/ (f* (r2f 2) (r2f (f*e_C*)))
                     (r2f (f*h_bar*))))
       ;; At this time, VWSIM does not support continuation of
       ;; simulations starting from time 0. What if we would like to
       ;; start the simulation at a non-zero initial voltage/phase???
       (phases (voltage-to-phase-help
                voltages hns (r2f 0) (r2f 0) constant)))
    phases))

(defthm rational-listp-voltage-to-phase
  (implies (symbol-rational-list-alistp records)
           (rational-listp (voltage-to-phase node records))))

(in-theory (disable voltage-to-phase))

; Some events for calculating the current through a JJ

(encapsulate
  ()
  (local
   (defthm len-0-not-consp
    (implies (= (len l) 0)
             (not (consp l)))))

  (defun jj-current-help
      (node+-vals     ;; voltages/phases of positive node
       node--vals     ;; voltages/phases of negative node
       node+-dp-vals  ;; derivatives of positive node voltage/phase
       node--dp-vals  ;; derivatives of negative node voltage/phase
       branch-vals    ;; voltage/phase of branch
       branch-dp-vals ;; derivative of branch
       icrit          ;; jj critical current
       vg             ;; jj gap voltage
       r0             ;; jj subgap resistance
       rn             ;; jj normal resistance
       cap            ;; jj capacitance
       sim-type       ;; simulation type: voltage or phase
       )
    (declare (xargs :guard (and (rational-listp node+-vals)
                                (rational-listp node--vals)
                                (rational-listp node+-dp-vals)
                                (rational-listp node--dp-vals)
                                (rational-listp branch-vals)
                                (rational-listp branch-dp-vals)
                                (rationalp icrit)
                                (rationalp vg)
                                (rationalp r0)
                                (rationalp rn)
                                (rationalp cap)
                                (not (= r0 0))
                                (not (= rn 0))
                                (symbolp sim-type)
                                (= (len node+-vals) (len node--vals))
                                (= (len node+-vals) (len node+-dp-vals))
                                (= (len node+-vals) (len node--dp-vals))
                                (= (len node+-vals) (len branch-vals))
                                (= (len node+-vals) (len branch-dp-vals)))))
    ;; I = (icrit*sin(phi(t))) + (capacitance * (dv/dt)) + (1/R)*v(t)
        (if (atom node+-vals)
            nil
          (b* (;; adjust parameters using area. We can optimize this
               ;; redundant calculation later.
               (DeltaV  (r2f (f*DeltaV*)))
               (Icfact  (r2f (f*Icfact*)))
               (Vgap-DV (f- (r2f vg) (f/ DeltaV (r2f 2))))
               (Vgap+DV (f+ (r2f vg) (f/ DeltaV (r2f 2))))

               (v (if (eq sim-type 'voltage) ;; jj voltage
                      (f- (car node+-vals)
                          (car node--vals))
                    (car branch-vals)))

               (phi (if (eq sim-type 'voltage) ;; jj phase
                        (car branch-vals)
                      (f- (car node+-vals)
                          (car node--vals))))

               (dp-v (if (eq sim-type 'voltage) ;; dv/dt
                         (f- (car node+-dp-vals)
                             (car node--dp-vals))
                       (car branch-dp-vals)))

               (r_in_Gap (f/ (r2f icrit) (f* Icfact DeltaV)))
               ;; we determine the non-linear resistance based on
               ;; the voltage across the jj
               (r (if (f< (f-abs v) Vgap-DV)
                      (r2f r0)
                    (if (f< (f-abs v) Vgap+DV)
                        (r2f r_in_Gap)
                      (r2f rn))))
               (current
                ;; jj-current function needs to be reloaded
                ;; because of f-sin. Consider putting this
                ;; function in vw-hdl/vw-eval.
                (f+ (f* (r2f icrit) (f-sin phi))
                    (f+ (f* (r2f cap) dp-v)
                        (f* (f-1/x r) v)))))
            (cons current
                  (jj-current-help (cdr node+-vals) (cdr node--vals)
                                   (cdr node+-dp-vals)
                                   (cdr node--dp-vals) (cdr branch-vals)
                                   (cdr branch-dp-vals)
                                   icrit vg r0 rn cap sim-type)))))
  )

(defun jj-ios-dps (occ)
  (declare (xargs :guard (occurrencep occ)))
  (case-match occ
    ((& 'b (node+ node-) (branch) . &)
     (list node+ node- branch
           (dp node+) (dp node-) (dp branch)))))

(defthm symbol-listp-jj-ios
  (implies (and (occurrencep occ)
                (equal (cadr occ) 'b))
           (symbol-listp (jj-ios-dps occ))))

(in-theory (disable jj-ios-dps))

(defun assoc-list (l r)
  (declare (xargs :guard (and (true-listp l)
                              (alistp r))))
  (if (atom l)
      nil
    ;; from key-val pair, just get the val
    (cons (cdr (assoc-equal (car l) r))
          (assoc-list (cdr l) r))))

(defun rational-list-listp (x)
  "A list of rational-number lists."
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (rational-listp (car x))
         (rational-list-listp (cdr x)))))

(defthm rational-list-listp-assoc-list
  (implies (symbol-rational-list-alistp r)
           (rational-list-listp (assoc-list l r))))

(in-theory (disable assoc-list))

(defthm rational-listp-car-rational-list-listp
  (implies (rational-list-listp l)
           (and (rational-listp (car l))
                (rational-listp (cadr l))
                (rational-listp (caddr l))
                (rational-listp (cadddr l))
                (rational-listp (car (cddddr l)))
                (rational-listp (car (cdr (cddddr l)))))))

;; The following events are for calculating information
;; (voltage,phase,current) that is not stored in the simulation state
;; (records)

;; calculate the current through the JJ for every time step in the
;; simulation state
(defun jj-current (jj-occ-name occs records sim-type)
  ;; calculates the current through a JJ using the simulation
  ;; records
  (declare (xargs :guard (and (symbolp jj-occ-name)
                              (occurrence-listp occs)
                              (symbol-rational-list-alistp records)
                              (alist-entry-consp records)
                              (symbolp sim-type))
                  :guard-hints
                  (("Goal" :in-theory (e/d (occurrencep
                                            occurrence-listp f/)
                                           (member-equal not endp eq vw-eval
                                                         vw-eval-termp))))))
  (b* ((occ (assoc-equal jj-occ-name occs))
       ((unless (and (occurrencep occ)
                     (equal (cadr occ) 'b)))
        (cw "jj-current: extraced a non-occurrence from occs.~%"))
       (nodes-brs-dps (jj-ios-dps occ))
       (list-of-vals (assoc-list nodes-brs-dps records))
       (node+-vals    (car list-of-vals))
       (node--vals    (cadr list-of-vals))
       (branch-vals   (caddr list-of-vals))
       (node+-dp-vals (cadddr list-of-vals))
       (node--dp-vals (car (cddddr list-of-vals)))
       ;; will need these values for jj-current in phase-mode
       (?branch-dp-vals   (car (cdr (cddddr list-of-vals))))
       ((unless (and (= (len node+-vals) (len node--vals))
                     (= (len node+-vals) (len node+-dp-vals))
                     (= (len node+-vals) (len node--dp-vals))
                     (= (len node+-vals) (len branch-vals))
                     (= (len node+-vals) (len branch-dp-vals))))
        (cw "jj-current: some lists in the records are not the same length!~%"))
       (params (car (cddddr occ)))
       (icrit (r2f (unquote (car params))))
       (area  (r2f (unquote (cadr params))))
       (vg    (r2f (unquote (caddr params))))
       (rn    (r2f (unquote (cadddr params))))
       (r0    (r2f (unquote (car (cddddr params)))))
       (cap   (r2f (unquote (car (cdr (cddddr params))))))
       ;; adjust JJ parameters using area
       (r0 (f/ r0 area))
       (rn  (f/ rn  area))
       (icrit (f* icrit area))
       (cap (f* cap area)))
    (jj-current-help node+-vals node--vals node+-dp-vals
                     node--dp-vals branch-vals branch-dp-vals icrit vg
                     r0 rn cap sim-type)))

(defun subtract-lists (l1 l2)
  "Subtract two lists"
  (declare (xargs :guard (and (rational-listp l1)
                              (rational-listp l2))))
  (if (or (atom l1) (atom l2))
      nil
    (cons (- (car l1)
             (car l2))
          (subtract-lists (cdr l1) (cdr l2)))))

(defun resistor-current-help (l1 l2 s)
  (declare (xargs :guard (and (rational-listp l1)
                              (rational-listp l2)
                              (rationalp s))))
  (if (or (atom l1) (atom l2))
      nil
    (cons (f* (f- (car l1) (car l2))
             s)
          (resistor-current-help (cdr l1) (cdr l2) s))))

(defthm rational-listp-assoc-symbol-rational-list-alistp
  (implies (symbol-rational-list-alistp r)
           (rational-listp (cdr (assoc key r)))))

(defun resistor-current (occ records sim-type)
  (declare (xargs :guard (and (occurrencep occ)
                              (symbol-rational-list-alistp records)
                              (alist-entry-consp records)
                              (symbolp sim-type))
                  :guard-hints (("Goal" :in-theory (enable f*)))))
  (case-match occ
    ((& 'r (node+ node-) (&) (resistance))
     ;; since Ohm's law requires a constant temperature (and thus a
     ;; constant resistance), we assume that the resistance is
     ;; constant.
     (let ((resistance-val (unquote resistance)))
       (if (eq sim-type 'voltage)
           (let* ((voltages+ (cdr (assoc node+ records)))
                  (voltages- (cdr (assoc node- records))))
             (resistor-current-help voltages+ voltages- (f-1/x (r2f resistance-val))))
         (let* ((phase-derivs+ (cdr (assoc (dp node+) records)))
                (phase-derivs- (cdr (assoc (dp node-) records)))
                (s-val (f/ (r2f (f*phi0*))
                           (f* (r2f 2)
                               (f* (r2f (f*pi*)) (r2f resistance-val))))))
           ;; i = phi0/(2piR) * (dp phase)
           (resistor-current-help phase-derivs+ phase-derivs-
                                  s-val)))))))

(defun devv (occ records sim-type)
  ;; calculates the voltage across a device
  (declare (xargs :guard (and (occurrencep occ)
                              (symbol-rational-list-alistp records)
                              (symbolp sim-type))
                  :guard-hints (("Goal" :in-theory (e/d () (member-equal))))))
  (case-match occ
    ((& component (node+ node-) (branch) . &)
     (if (eq component 'k)
         (cw "devv: the mutual inductance is not a device, and hence
         the results are not stored.~%~p0.~%"
             occ)
       (if (eq sim-type 'voltage)
           (let ((node+-vals (cdr (assoc node+ records)))
                 (node--vals (cdr (assoc node- records))))
             (subtract-lists node+-vals node--vals))
         ;; in a phase-based simulation, the JJ's branch stores the
         ;; voltage across it
         (if (eq component 'b)
             (cdr (assoc-equal branch records))
         ;; in phase-based simulation, we convert the phase values to
         ;; voltages and then subtract to get the device voltage
         (subtract-lists (phase-to-voltage node+ records)
                         (phase-to-voltage node- records))))))
    ;; four-node devices (only the transmission line)
    ((& 't (node0+ node0- node1+ node1-) . &)
     (if (eq sim-type 'voltage)
         (let ((node0+-vals (cdr (assoc node0+ records)))
               (node0--vals (cdr (assoc node0- records)))
               (node1+-vals (cdr (assoc node1+ records)))
               (node1--vals (cdr (assoc node1- records))))
           ;; The voltages across the transmission line are the
           ;; voltage across the entrance nodes and the voltage across
           ;; the exit nodes.
           (list (subtract-lists node0+-vals node0--vals)
                 (subtract-lists node1+-vals node1--vals)))
       ;; In phase-based simulation, convert phase values to voltage
       ;; values
       (list (subtract-lists (phase-to-voltage node0+ records)
                             (phase-to-voltage node0- records))
             (subtract-lists (phase-to-voltage node1+ records)
                             (phase-to-voltage node1- records)))))
    (& (cw "devv: the results of the specified device are not stored.~%~p0.~%"
           occ))))

(defthm true-listp-devv
  (implies (and (occurrencep occ)
                (symbol-rational-list-alistp records))
           (true-listp (devv occ records sim-type)))
  :hints
  (("Goal" :in-theory (disable member-equal no-duplicatesp-equal
                               occurrencep)))
  :rule-classes :type-prescription)

(in-theory (disable devv))

(defun devi (occ records flat-netlist sim-type)
  ;; calculates the current through a device
  (declare (xargs :guard (and (occurrencep occ)
                              (symbol-rational-list-alistp records)
                              (alist-entry-consp records)
                              (symbolp sim-type)
                              (occurrence-listp flat-netlist))))
  (case-match occ
    ;; one-branch devices
    ((& component & (branch) . &)
     (if (eq component 'k)
         (cw "devi: the mutual inductance is not a device, and hence
         the results are not stored.~%~p0.~%"
             occ)
       ;; the JJ's branch stores phase when sim-type is voltage
       ;;                 stores voltage when sim-type is phase
       (if (equal component 'b)
           (jj-current (car occ) flat-netlist records sim-type)
         (if (equal component 'r)
             (resistor-current occ (make-fast-alist records) sim-type)
           ;; other components with only one branch store the current
           ;; through the device in the branch
           (let ((currents (cdr (assoc-equal branch records))))
             currents)))))
     ;; two-branch devices (only the transmission line)
    ((& 't & (br0 br1) . &)
     ;; During simulation, we record the current through the entrance
     ;; and the exit of the transmission line.
     (let ((currents-in (cdr (assoc-equal br0 records)))
           (currents-out (cdr (assoc-equal br1 records))))
       (list currents-in currents-out)))
    (& (cw "devi: the results of the specified device are not stored.~%~p0.~%"
           occ))))

(defthm true-listp-devi
  (implies (and (occurrencep occ)
                (symbol-rational-list-alistp records))
           (true-listp (devi occ records flat-netlist sim-type)))
  :rule-classes :type-prescription
  :hints
  (("Goal" :in-theory (disable member-equal
                               no-duplicatesp-equal
                               jj-current
                               resistor-current
                               make-fast-alist
                               occurrencep))))

(in-theory (disable devi))

(defun phase-fn (occ records sim-type)
  ;; calculates the phase across a device
  (declare (xargs :guard (and (occurrencep occ)
                              (symbol-rational-list-alistp records)
                              (symbolp sim-type))
                  :guard-hints (("Goal" :in-theory (disable member-equal)))))
  (case-match occ
    ;; one-branch devices
    ((& component (node+ node-) (branch) . &)
     (if (eq component 'k)
         (cw "phase: the mutual inductance is not a device, and hence
         the results are not stored.~%~p0.~%"
             occ)
       (if (eq sim-type 'voltage)
           ;; in a voltage-simulation, the JJ's branch stores the
           ;; phase across it
           (if (eq component 'b)
               (cdr (assoc branch records))
             ;; for other components, we need to calculate the phase
             ;; across it.
             (subtract-lists (voltage-to-phase node+ records)
                             (voltage-to-phase node- records)))
         ;; in a phase-based simulation, we simply subtract the values
         ;; of the nodes
         (let ((node+-vals (cdr (assoc node+ records)))
               (node--vals (cdr (assoc node- records))))
           (subtract-lists node+-vals node--vals)))))
    ((& 't (node0+ node0- node1+ node1-) . &)
     (if (eq sim-type 'voltage)
         ;; The phases across the transmission line are the phase
         ;; across the entrance nodes and the phase across the exit
         ;; nodes.
         (list (subtract-lists (voltage-to-phase node0+ records)
                               (voltage-to-phase node0- records))
               (subtract-lists (voltage-to-phase node1+ records)
                               (voltage-to-phase node1- records)))
       (let ((node0+-vals (cdr (assoc node0+ records)))
             (node0--vals (cdr (assoc node0- records)))
             (node1+-vals (cdr (assoc node1+ records)))
             (node1--vals (cdr (assoc node1- records))))
         (list (subtract-lists node0+-vals node0--vals)
               (subtract-lists node1+-vals node1--vals)))))
    (& (cw "devv: the results of the specified device are not stored.~%~p0.~%"
           occ))))

(defthm true-listp-phase-fn
  (implies (and (occurrencep occ)
                (symbol-rational-list-alistp records))
           (true-listp (phase-fn occ records sim-type)))
  :rule-classes :type-prescription
  :hints
  (("Goal" :in-theory (disable occurrencep))))

(in-theory (disable phase-fn))

(defun vw-output-request-alistp (requests)
  (declare (xargs :guard t))
  (if (atom requests)
      (null requests)
    (let ((pair (car requests)))
      (and (consp pair)
           (let ((type (car pair))
                 (name (cdr pair)))
             (and
              (symbolp type)
              (member-eq type '(NODEV NODEP DEVV DEVI PHASE))
              (symbolp name)
              (vw-output-request-alistp (cdr requests))))))))

(encapsulate
  ()

  (local (defthm consp-cdr-occurrencep
         (implies (occurrencep occ)
                  (consp (cdr occ)))))

  (defun print-records (records prints flat-netlist sim-type old-concat-char
                                vw-concat-char)
    ;; Filters the simulation state (records) to only return the
    ;; requested (.print) values in the cir file.
    (declare (xargs :guard (and (symbol-rational-list-alistp records)
                                (alist-entry-consp records)
                                (vw-output-request-alistp prints)
                                (occurrence-listp flat-netlist)
                                (symbolp sim-type)
                                (characterp old-concat-char)
                                (standard-char-p old-concat-char)
                                (characterp vw-concat-char)
                                (standard-char-p vw-concat-char))
                    :guard-hints (("Goal" :in-theory
                                   (disable occurrencep member-equal)))))
    (if (atom prints)
        nil
      (let* ((print (car prints))
             (type (car print))
             (name (cdr print)))
        (case type
          (NODEV (let ((node-vals (assoc name records)))
                   (if node-vals
                       (let* ((vals (cdr node-vals))
                              (voltages (if (eq sim-type 'voltage)
                                            vals
                                          (phase-to-voltage name records)))
                              (new-name (gen-output-name name "V"
                                                         old-concat-char
                                                         vw-concat-char))
                              (new-entry (cons new-name voltages)))
                         (cons new-entry (print-records records (cdr prints)
                                                        flat-netlist
                                                        sim-type
                                                        old-concat-char
                                                        vw-concat-char)))
                     (prog2$
                      (cw "print-records: the node ~p0 does not exist.~%"
                          name)
                      (print-records records (cdr prints)
                                     flat-netlist
                                     sim-type
                                     old-concat-char
                                     vw-concat-char)))))
          (NODEP (let ((node-vals (assoc name records)))
                   (if node-vals
                       (let* ((vals (cdr node-vals))
                              (phases (if (eq sim-type 'voltage)
                                          (voltage-to-phase name records)
                                        vals))
                              (new-name (gen-output-name name "P" old-concat-char
                                                         vw-concat-char))
                              (new-entry (cons new-name phases)))
                         (cons new-entry (print-records records (cdr prints)
                                                        flat-netlist
                                                        sim-type
                                                        old-concat-char
                                                        vw-concat-char)))
                     (prog2$
                      (cw "print-records: the node ~p0 does not exist.~%"
                          name)
                      (print-records records (cdr prints)
                                     flat-netlist
                                     sim-type
                                     old-concat-char
                                     vw-concat-char)))))
          (DEVV (b* ((occ (assoc-equal name flat-netlist))
                     ((unless occ)
                      (prog2$
                       (cw "print-records: the device ~p0 does not exist.~%"
                           name)
                       (print-records records (cdr prints)
                                      flat-netlist
                                      sim-type
                                      old-concat-char
                                      vw-concat-char)))
                     (voltages (devv occ records sim-type)))
                  ;; transmission lines have an entrance and exit
                  ;; voltage.
                  (if (eq (cadr occ) 't)
                      (b* ((voltage-in (car voltages))
                           (voltage-out (cadr voltages))
                           (new-name-in (gen-output-name name "V"
                                                         old-concat-char
                                                         vw-concat-char))
                           (new-name-in (string-append new-name-in "-in"))
                           (new-name-out (gen-output-name name "V"
                                                          old-concat-char
                                                          vw-concat-char))
                           (new-name-out (string-append new-name-out "-out"))
                           (new-entry1 (cons new-name-in voltage-in))
                           (new-entry2 (cons new-name-out voltage-out)))
                        (cons new-entry1
                              (cons new-entry2
                                    (print-records records (cdr prints)
                                                   flat-netlist
                                                   sim-type
                                                   old-concat-char
                                                   vw-concat-char))))

                    (let* ((new-name (gen-output-name name "V" old-concat-char
                                                      vw-concat-char))
                           (new-entry (cons new-name voltages)))
                      ;; can you ask for the devv across a mutual
                      ;; inductance? Nope. It is not a device, and hence
                      ;; results can't be stored.
                      (cons new-entry (print-records records (cdr prints)
                                                     flat-netlist
                                                     sim-type
                                                     old-concat-char
                                                     vw-concat-char))))))
          (DEVI (b* ((occ (assoc-equal name flat-netlist))
                     ((unless occ)
                      (prog2$
                       (cw "print-records: the device ~p0 does not exist.~%"
                           name)
                       (print-records records (cdr prints)
                                      flat-netlist
                                      sim-type
                                      old-concat-char
                                      vw-concat-char)))
                     (currents (devi occ records flat-netlist sim-type)))
                  ;; transmission lines have an entrance and exit
                  ;; current
                  (if (eq (cadr occ) 't)
                      (b* ((current-in (car currents))
                           (current-out (cadr currents))
                           (new-name-in (gen-output-name name "I"
                                                         old-concat-char
                                                         vw-concat-char))
                           (new-name-in (string-append new-name-in "-in"))
                           (new-name-out (gen-output-name name "I"
                                                          old-concat-char
                                                          vw-concat-char))
                           (new-name-out (string-append new-name-out "-out"))
                           (new-entry1 (cons new-name-in current-in))
                           (new-entry2 (cons new-name-out current-out)))
                        (cons new-entry1
                              (cons new-entry2
                                    (print-records records (cdr prints)
                                                   flat-netlist
                                                   sim-type
                                                   old-concat-char
                                                   vw-concat-char))))
                    ;; all of the other devices have only one terminal (branch).
                    (let* ((new-name (gen-output-name name "I" old-concat-char
                                                      vw-concat-char))
                           (new-entry (cons new-name currents)))
                      (cons new-entry (print-records records (cdr prints)
                                                     flat-netlist
                                                     sim-type
                                                     old-concat-char
                                                     vw-concat-char))))))
          (PHASE (b* ((occ (assoc-equal name flat-netlist))
                      ((unless occ)
                       (prog2$
                        (cw "print-records: the device ~p0 does not exist.~%"
                            name)
                        (print-records records (cdr prints)
                                       flat-netlist
                                       sim-type
                                       old-concat-char
                                       vw-concat-char)))
                      (phases (phase-fn occ records sim-type)))
                   (if (eq (cadr occ) 't)
                       (b* ((phase-in (car phases))
                            (phase-out (cadr phases))
                            (new-name-in (gen-output-name name "P"
                                                          old-concat-char
                                                          vw-concat-char))
                            (new-name-in (string-append new-name-in "-in"))
                            (new-name-out (gen-output-name name "P"
                                                           old-concat-char
                                                           vw-concat-char))
                            (new-entry1 (cons new-name-in phase-in))
                            (new-entry2 (cons new-name-out phase-out)))
                         ;; transmission lines have an entrance and
                         ;; exit phase.
                         (cons new-entry1
                               (cons new-entry2
                                     (print-records records (cdr prints)
                                                    flat-netlist
                                                    sim-type
                                                    old-concat-char
                                                    vw-concat-char))))
                     ;; all of the other devices have only one terminal (branch).
                     (let* ((new-name (gen-output-name name "P"
                                                       old-concat-char
                                                       vw-concat-char))
                            (new-entry (cons new-name phases)))
                       (cons new-entry (print-records records (cdr prints)
                                                      flat-netlist
                                                      sim-type
                                                      old-concat-char
                                                      vw-concat-char))))))
          (otherwise (print-records records (cdr prints) flat-netlist sim-type
                                    old-concat-char vw-concat-char)))))))


(defun print-device-reqs (devices)
  (declare (xargs :guard t))
  (if (atom devices)
      nil
    (let ((device (car devices)))
      (list* (cons 'DEVV device)
             (cons 'DEVI device)
             (cons 'PHASE device)
             (print-device-reqs (cdr devices))))))

(defun print-node-reqs (nodes)
  (declare (xargs :guard t))
  (if (atom nodes)
      nil
    (let ((node (car nodes)))
      (list* (cons 'NODEV node)
             (cons 'NODEP node)
             (print-node-reqs (cdr nodes))))))

(defun all-print-reqs (nodes devices)
  (declare (xargs :guard t))
  (append (print-node-reqs nodes)
          (print-device-reqs devices)))

#||

Things to do

-> .param

||#


#||


What follows was taken from the JoSIM documentation. This
documentation is incomplete and does not agree with the behavior of
JoSIM; for example, the following input is not recognized:

RRP1 net@3 +
gnd 0.4

Taken verbatim from JoSIM manual:

In this section we will attempt to provide the user with a
comprehensive guide of the available syntax within JoSIM

JoSIM is CaSe InSeNsItIvE as each line is cast to uppercase upon
read-in.

Each line follows similar syntax which uses the first non-blank space
character as identifier. Each identifier tells JoSIM how to handle
that specific line.

Identifiers that start with a letter relate to physical components in
the design, e.g. L, C, R. Lines of this kind almost always follows the
same syntax in that it requires a label and two nodes. These nodes can
be alphanumeric with the restriction of 0 and GND which indicate a
grounded node. Additionally, the use of period (.) or vertical
bars (|) in label or node names are prohibited as these are reserved
pcharacters within JoSIM.

Lines that start with a period (.) indicate that the line relates in
some way to simulation control. In this case whatever follows the
period identifies the control, e.g. .tran, .print, .end.

Comments are lines that start with an asterisk (*) or a pound sign
(#). Comments are meant to be in a line of their own and will not work
if placed at the end of a line.

Lines that end with a plus sign (+) indicate that the line that
follows is a continuation of this line. Internally the two lines will
be combined.

In most cases the VALUE of a component can be replaced by a variable
name or an expression. Variables can be defined using the .PARAM
control and expressions can be evaluated by encapsulating the
expression in braces ({}). These will be discussed in detail further.

Values in JoSIM can be modified with engineering notation or through
suffixes. A list of the available suffixes is found below:

Suffix	Meaning	Engineering Notation Equivalent
F	Femto	1E-15
P	Pico	1E-12
N	Nano	1E-9
U	Micro	1E-6
M	Milli	1E-3
K	Kilo	1E3
MEG	Mega	1E6
X
G	Giga	1E9
T	Terra	1E12
We will now run through all the available physical components and
their limitations. Any parameter surrounded by square brackets are
optional and nested square brackets mean that the encapsulated
parameter relies on the existance of the previous.

||#
