; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
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


(in-package "ACL2")

(include-book "defdoc")

(include-book "xdoc/top" :dir :system)

;;; The following legacy doc string was replaced Nov. 2014 by the
;;; auto-generated defxdoc form just below.
; (def::doc RULE-SETS
;
;   :one-liner "Machinery for organizing and versioning dynamic
; sets of rules"
;
;   :details (docstring (\n)
; "  ACL2 enables users to define named collections of rules,
; "(docref"theories")", that can be used in conjunction with
; "(docref"in-theory")" events to manage the theory state of ACL2.
; Defining a theory, however, requires that all of the rules in the
; theory be known at the point at which the theory is defined.
;
;   RULE-SETS enable users to define named collections of rules
; (RULE-SETS) and to incrementally modify that collection as necessary
; to maintain a desired theory philosophy.
;
;   Each rule set is associated with a particular set name as well as a
; collection of versions.  Set names and versions may be any eqlablep
; object.  For example, the rule set:
;
;   `(zed . alpha)
;
;   Refers to the alpha version of rule set zed.
;
;   Rule sets are expected to have applications in both theory
; management and library development.
;
;   Library developers will want to use rule sets to isolate different
; proof styles as well as different classes of rules.  It seems unlikely
; that one would want to version rule classes used in this style unless,
; perhaps, it were to support a proof methodology such as phased
; rewriting.
;
;   Libraries themselves should be associated with umbrella rule classes
; that cover all of the crucial functions and theories developed within
; the library.  Here, versioning is the key to robust proof development
; in the face of library extensions.  When a library is released, it
; should be done so under a specific version tag.  Subsequent extensions
; of that library should be performed under different version tags.
;
;   Library rule classes should be orthoganal to methodological rule
; classes.
;
;   It is possible to classify a given rule under several different rule
; classes.  Every classified rule is classified under a specific library
; (by default).  It may also be classified under one or more
; methodological rule classes.
;
;   "(docref"def::rule-set")"
;
; "))

(defxdoc rule-sets
  :parents (rule-sets)
  :short "Machinery for organizing and versioning dynamic
sets of rules"
  :long "<p><br></br> ACL2 enables users to define named collections of rules,
   See @(see theories), that can be used in conjunction with See @(see
   in-theory) events to manage the theory state of ACL2.  Defining a theory,
   however, requires that all of the rules in the theory be known at the point
   at which the theory is defined.</p>

 <p>RULE-SETS enable users to define named collections of rules (RULE-SETS) and
 to incrementally modify that collection as necessary to maintain a desired
 theory philosophy.</p>

 <p>Each rule set is associated with a particular set name as well as a
 collection of versions.  Set names and versions may be any eqlablep object.
 For example, the rule set:</p>

 <p>`(zed . alpha)</p>

 <p>Refers to the alpha version of rule set zed.</p>

 <p>Rule sets are expected to have applications in both theory management and
 library development.</p>

 <p>Library developers will want to use rule sets to isolate different proof
 styles as well as different classes of rules.  It seems unlikely that one
 would want to version rule classes used in this style unless, perhaps, it were
 to support a proof methodology such as phased rewriting.</p>

 <p>Libraries themselves should be associated with umbrella rule classes that
 cover all of the crucial functions and theories developed within the library.
 Here, versioning is the key to robust proof development in the face of library
 extensions.  When a library is released, it should be done so under a specific
 version tag.  Subsequent extensions of that library should be performed under
 different version tags.</p>

 <p>Library rule classes should be orthoganal to methodological rule
 classes.</p>

 <p>It is possible to classify a given rule under several different rule
 classes.  Every classified rule is classified under a specific library (by
 default).  It may also be classified under one or more methodological rule
 classes.</p>

 <p>See @(see def::rule-set)</p>")

;;; The following legacy doc string was replaced Nov. 2014 by the
;;; auto-generated defxdoc form just below.
; (def::doc def::rule-set
;
;   :one-liner "A macro for defining a new rule set"
;
;   :details (docstring (\n)
;
; "New rule sets can be defined using def::rule-set."))

(defxdoc def::rule-set
  :parents (def::rule-set)
  :short "A macro for defining a new rule set"
  :long "<p><br></br> New rule sets can be defined using def::rule-set.</p>")