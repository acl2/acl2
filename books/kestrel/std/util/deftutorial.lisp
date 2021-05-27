; Standard Utilities Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "system/pseudo-event-form-listp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation deftutorial :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftutorial-gen-deftop ((tut-name symbolp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the macro to define the top page of the tutorial."
  :long
  (xdoc::topstring-p
   "The generated macro stores information about the top page into the table.
    The information consists of a pair in the table,
    whose key is the keyword @(':top')
    and whose value is a list @('(parents text1 text2 ...)')
    obtained from the arguments of the macro.")
  (b* ((deftop (packn-pos (list 'def- tut-name '-top) tut-name))
       (deftop-fn (add-suffix deftop "-FN"))
       (tut-table (add-suffix tut-name "-TABLE")))
    `((defun ,deftop-fn (top-parents top-text)
        (b* ((top (cons top-parents top-text)))
          `(table ,',tut-table :top ',top)))
      (defmacro ,deftop (top-parents &rest top-text)
        `(make-event (,',deftop-fn ',top-parents ',top-text))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftutorial-gen-defpage ((tut-name symbolp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the macro to define a (non-top) page of the tutorial."
  :long
  (xdoc::topstring-p
   "The generated macro stores information about these pages into the table.
    The information consists of a pair in the table,
    whose key is the keyword @(':pages')
    and whose value is a list of (information about) pages,
    in reverse order of introduction (i.e. new pages are @(tsee cons)ed).
    Each element of the list is a list @('(name title text1 text2 ...)')
    obtained from the arguments of the macro.")
  (b* ((defpage (packn-pos (list 'def- tut-name '-page) tut-name))
       (defpage-fn (add-suffix defpage "-FN"))
       (tut-table (add-suffix tut-name "-TABLE")))
    `((defun ,defpage-fn (page-name page-title page-text wrld)
        (b* ((pages (cdr (assoc-eq :pages (table-alist ',tut-table wrld))))
             (page-name (packn-pos (list ',tut-name '- page-name) ',tut-name))
             (page (list* page-name page-title page-text))
             (new-pages (cons page pages)))
          `(table ,',tut-table :pages ',new-pages)))
      (defmacro ,defpage (page-name page-title &rest page-text)
        `(make-event
          (,',defpage-fn ',page-name ',page-title ',page-text (w state)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftutorial-gen-deftopics ((tut-name symbolp) (tut-title stringp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the macro to define the XDOC topics of the tutorial."
  :long
  (xdoc::topstring-p
   "The generated macro retrieves from the table
    the information about top and non-top pages,
    and creates @(tsee defxdoc) forms for each of them.
    The (non-top) pages are reversed, so they are in the order of introduction
    (this is not necessary, but this way
    we keep the ACL2 history more consistent).
    We extend the long string of each page
    with the appropriate links to other pages;
    we use empty boxes to create a line of separation
    just before those links.")
  (b* ((deftopics (packn-pos (list 'def- tut-name '-topics) tut-name))
       (deftopics-fn (add-suffix deftopics "-FN"))
       (deftopics-loop (add-suffix deftopics "-LOOP"))
       (tut-table (add-suffix tut-name "-TABLE")))
    `((defun ,deftopics-loop (pages previous-name previous-title)
        (b* (((when (endp pages)) nil)
             (page (car pages))
             (page-name (car page))
             (page-title (cadr page))
             (page-text (cddr page))
             (previous-link?
              (and previous-name
                   `(xdoc::p "<b>Previous:</b> "
                             (xdoc::seetopic ,(symbol-name previous-name)
                                             ,previous-title))))
             ((mv next-name next-title)
              (if (consp (cdr pages))
                  (mv (car (cadr pages)) (cadr (cadr pages)))
                (mv nil nil)))
             (next-link?
              (and (consp (cdr pages))
                   `(xdoc::p "<b>Next:</b> "
                             (xdoc::seetopic ,(symbol-name next-name)
                                             ,next-title))))
             (topic `(defxdoc ,page-name
                       :parents (,',tut-name)
                       :short ,(concatenate 'string
                                            ,tut-title ": " page-title ".")
                       :long
                       (xdoc::topstring
                        ,@page-text
                        (xdoc::box)
                        ,@(and previous-link? (list previous-link?))
                        ,@(and next-link? (list next-link?)))))
             (topics (,deftopics-loop (cdr pages) page-name page-title)))
          (cons topic topics)))
      (defun ,deftopics-fn (wrld)
        (b* ((top (cdr (assoc-eq :top (table-alist ',tut-table wrld))))
             (pages (cdr (assoc-eq :pages (table-alist ',tut-table wrld))))
             (pages (reverse pages))
             (top-parents (car top))
             (top-text (cdr top))
             (start-link?
              (and (consp pages)
                   `(xdoc::p "<b>Start:</b> "
                             (xdoc::seetopic ,(symbol-name (car (car pages)))
                                             ,(cadr (car pages))))))
             (top-topic
              `(defxdoc ,',tut-name
                 :parents ,top-parents
                 :short ,(concatenate 'string ,tut-title ".")
                 :long
                 (xdoc::topstring
                  ,@top-text
                  (xdoc::box)
                  ,@(and start-link? (list start-link?)))))
             (topics (,deftopics-loop pages nil nil)))
          `(progn
             ,top-topic
             ,@topics)))
      (defmacro ,deftopics ()
        `(make-event (,',deftopics-fn (w state)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftutorial-gen-section ((tut-name symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the macro to define a section in a tutorial page."
  :long
  (xdoc::topstring-p
   "We use a level-5 heading to keep it relatively small.")
  (b* ((tut-section (add-suffix tut-name "-SECTION")))
    `(defmacro ,tut-section (title)
       `(xdoc::h5 ,title))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftutorial-fn ((tut-name symbolp) (tut-title stringp))
  :returns (event pseudo-event-formp)
  :short "Generate all the macros to build the tutorial."
  `(progn
     ,@(deftutorial-gen-deftop tut-name)
     ,@(deftutorial-gen-defpage tut-name)
     ,@(deftutorial-gen-deftopics tut-name tut-title)
     ,(deftutorial-gen-section tut-name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection deftutorial-definition
  :short "Definition of the @(tsee deftutorial) macro."
  (defmacro deftutorial (tut-name tut-title)
    (declare (xargs :guard (and (symbolp tut-name) (stringp tut-title))))
    `(make-event (deftutorial-fn ',tut-name ,tut-title))))
