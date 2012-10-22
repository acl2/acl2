; Copyright (C) 2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original authors:  Sol Swords & Jared Davis  ({sswords,jared}@centtech.com)

(in-package "ACL2")

(include-book "regex-parse")
(include-book "regex-exec")
(include-book "str/case-conversion" :dir :system)


(local (in-theory (enable length-equiv length)))

(defun do-regex-match-precomp (str regex opts)
  (declare (xargs :guard (and (regex-p regex)
                              (stringp str)
                              (parse-opts-p opts))))
  (b* ((transstr (if (parse-options-case-insensitive opts)
                     (str::downcase-string str)
                   str))
       ((mv ?matchp whole substrs)
        (match-regex regex transstr str)))
    (mv whole substrs)))

;; returns:
;;  (mv error-msg whole-match substrs) ?
(defun do-regex-match (str pat opts)
  (declare (xargs :guard (and (stringp pat)
                              (stringp str)
                              (parse-opts-p opts))))
  (b* ((pat (if (parse-options-case-insensitive opts)
                (str::downcase-string pat)
              pat))
       (regex (regex-do-parse pat opts))
       ((when (stringp regex))
        (mv regex nil nil))
       ((mv whole substrs)
        (do-regex-match-precomp str regex opts)))
    (mv nil whole substrs)))


(def-b*-binder match
  (declare (xargs :guard (and (consp forms) (not (cdr forms))
                              (true-listp args))))
  (b* ((string (car forms)) ;; string to match against the pattern
       (pat (car args))
       (options (cdr args))
       (regex-type
        (b* ((bre (member :b args))
             (ere (member :e args))
             (fixed (member :f args))
             ((when (> (+ (if bre 1 0)
                          (if ere 1 0)
                          (if fixed 1 0))
                       1))
              (er hard? 'patbind-match
                  "more than one regex type argument supplied"))
             ((when bre) 'bre)
             ((when fixed) 'fixed))
          'ere))
       (regex-opts (parse-options
                    regex-type nil nil nil (consp (member :i options))))
       (call (if (stringp pat)
                 (b* ((pat (if (parse-options-case-insensitive regex-opts)
                               (str::downcase-string pat)
                             pat))
                      (regex (regex-do-parse pat regex-opts))
                      ((when (stringp regex))
                       (er hard? 'patbind-match
                           "Regex parse error: ~s0~%" regex)))
                   `(do-regex-match-precomp ,string ',regex ',regex-opts))
               `(do-regex-match ,string ,pat ',regex-opts)))
       (full-var (cadr (member :full options)))
       (substr-vars (cadr (member :substrs options)))
       (error-msg (cadr (member :error-msg options))))
    `(b* ((,(if (stringp pat)
               `(mv ,(or full-var '&)
                    ,(if substr-vars
                         `(nths . ,substr-vars)
                       '&))
              `(mv ,(or error-msg '&)
                   ,(or full-var '&)
                   ,(if substr-vars
                         `(nths . ,substr-vars)
                       '&)))
           ,call))
       ,rest-expr)))

;; Examples
(make-event
 (b* ((res1-ok
       (equal
        
        (b* (((match "ab([def]*)\\1([gh])" :i
                     :full f
                     :substrs (a b))
              "cdeAbfdEfDeghIj"))
          (list a b f))

        '("fdE" "g" "AbfdEfDeg")))
      (res2-ok
       (equal

        (b* ((pattern "ab([def]*)\\1([gh])")
             (string "cdeAbfdEfDeghIj")
             ((match  pattern :i
                      :full f
                      :substrs (a b)
                      :error-msg e)
              string))
          (list e a b f))

        '(NIL "fdE" "g" "AbfdEfDeg")))

      (res3-ok
       (equal

        ;; using recursive binders
        (b* ((pattern "ab([def]*)\\1([gh])")
             (string "cdeAbfdEfDeghIj")
             ((match  pattern :i
                      :full ?f  ;; ignorable
                      :substrs ((the string a) ;; type
                                &) ;; not bound
                      ;; error msg not present
                      )
              string))
          (list a f))

        '("fdE" "AbfdEfDeg"))))

      
   (if (and res1-ok res2-ok res3-ok)
       '(value-triple :ok)
     (er hard? 'regex-ui
         "One of the tests failed~%"))))

