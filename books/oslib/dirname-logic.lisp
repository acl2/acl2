; OSLIB -- Operating System Utilities
; Copyright (C) 2013-2014 Centaur Technology
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

(in-package "OSLIB")
(include-book "read-acl2-oracle")
(include-book "std/util/define" :dir :system)
(local (xdoc::set-default-parents oslib))

(define basename
  :parents (oslib)
  :short "Remove the leading directory part from a path."
  ((path stringp "Path to process.")
   &optional (state 'state))
  :returns (mv (err     "NIL on success or an error @(see msg) on failure.")
               (basename stringp :rule-classes :type-prescription
                         "Sensible only if there is no error.")
               (state state-p1 :hyp (force (state-p1 state))))

  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution we use Common Lisp functions to determine the part of @('path')
excluding its parent directory in some OS specific way.  See also @(see
dirname).</p>

<p>Examples (assuming a Unix style operating system):</p>

@({
     (basename \"/home/jared/hello.txt\")   -->  \"hello.txt\"
     (basename \"/home/jared/\")            -->  \"jared\"
     (basename \"/home/jared\")             -->  \"jared\"
})

<p>A special case is the basename of the root directory.  In this case we mimic
the (arguably nonsensical) behavior of the unix @('basename') command:</p>

@({
     (basename \"/\")                       -->  \"/\"
})"

  (declare (ignorable path))
  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv ?err1 val1 state) (read-acl2-oracle state))
       ((mv ?err2 val2 state) (read-acl2-oracle state))
       ((when val1)
        (mv val1 "" state))
       ((unless (stringp val2))
        (mv "Error with basename" "" state)))
    (mv nil val2 state)))

(define basename!
  :short "Remove the leading directory part of a path, or cause a hard error if
there is any problem."
  ((path stringp) &key (state 'state))
  :returns (mv (basename stringp :rule-classes :type-prescription)
               (state state-p1 :hyp (force (state-p1 state))))
  :long "<p>This is just a wrapper for @(see basename) that causes an error on
any failure.</p>"
  (b* (((mv err basename state) (basename path))
       ((when err)
        (raise "Basename failed: ~@0" err)
        (mv "" state)))
    (mv basename state)))

(define basenames
  :short "Removing leading directories from a list of paths."
  ((paths string-listp)
   &key (state 'state))
  :returns (mv (err "NIL on success or an error @(see msg) on failure.")
               (basenames string-listp "Sensible only if there is no error.")
               (state state-p1 :hyp (force (state-p1 state))))
  :long "<p>This just calls @(see basename) on every path in a list.</p>"
  (b* (((when (atom paths))
        (mv nil nil state))
       ((mv err name1 state) (basename (car paths)))
       ((when err) (mv err nil state))
       ((mv err names2 state) (basenames (cdr paths)))
       ((when err) (mv err nil state)))
    (mv nil (cons name1 names2) state)))


(define dirname
  :short "Strip the non-directory suffix from a path."
  ((path stringp "Path to process.")
   &optional (state 'state))
  :returns (mv (err     "NIL on success or an error @(see msg) on failure.")
               (dirname stringp :rule-classes :type-prescription
                        "Sensible only if there is no error.")
               (state state-p1 :hyp (force (state-p1 state))))

  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution we use Common Lisp functions to determine the parent directory of
@('path') in some OS specific way.  See also @(see basename).</p>

<p>Examples (assuming a Unix style operating system):</p>

@({
     (dirname \"/home/jared/hello.txt\")   -->  \"/home/jared/\"
     (dirname \"/home/jared/\")            -->  \"/home/\"
     (dirname \"/home/jared\")             -->  \"/home/\"
})

<p>A special case is the dirname of the root directory.  In this case we mimic
the (arguably nonsensical) behavior of the unix @('dirname') command:</p>

@({
     (dirname \"/\")                       -->  \"/\"
})"

  (declare (ignorable path))
  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv ?err1 val1 state) (read-acl2-oracle state))
       ((mv ?err2 val2 state) (read-acl2-oracle state))
       ((when val1)
        (mv val1 "" state))
       ((unless (stringp val2))
        (mv "Error with dirname" "" state)))
    (mv nil val2 state)))

(define dirname!
  :short "Strip the non-directory suffix from a file name, or cause a hard
error if there is any problem."
  ((path stringp) &key (state 'state))
  :returns (mv (dirname stringp :rule-classes :type-prescription)
               (state state-p1 :hyp (force (state-p1 state))))
  :long "<p>This is just a wrapper for @(see dirname) that causes an error on
any failure.</p>"
  (b* (((mv err dirname state) (dirname path))
       ((when err)
        (raise "Dirname failed: ~@0" err)
        (mv "" state)))
    (mv dirname state)))

(define dirnames
  :short "Strip non-directory suffixes from a list of file names."
  ((paths string-listp)
   &key (state 'state))
  :returns (mv (err "NIL on success or an error @(see msg) on failure.")
               (dirnames string-listp "Sensible only if there is no error.")
               (state state-p1 :hyp (force (state-p1 state))))
  :long "<p>This just calls @(see dirname) on every path in a list.</p>"
  (b* (((when (atom paths))
        (mv nil nil state))
       ((mv err name1 state) (dirname (car paths)))
       ((when err) (mv err nil state))
       ((mv err names2 state) (dirnames (cdr paths)))
       ((when err) (mv err nil state)))
    (mv nil (cons name1 names2) state)))
