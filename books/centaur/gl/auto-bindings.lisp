; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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
; auto-bindings.lisp
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "GL")
(include-book "gobject-types")
(include-book "../misc/numlist")
(include-book "std/util/bstar" :dir :system)
(program)

(defxdoc auto-bindings
  :parents (reference shape-specs)
  :short "Simplified shape specifiers for @(':g-bindings')."
  :long "<p>The @('auto-bindings') function lets you create simple @(see
shape-specs) in an easy way.  Here is an example:</p>

@({
 (def-gl-thm foo
   ...
   :g-bindings (auto-bindings                          ; expands to:
                (:nat opcode 8)                        ; g-integer with indices 0-8
                (:int multiplier 16)                   ; g-integer with indices 9-25
                (:bool enable)                         ; g-boolean with index 26
                (:mix (:nat a-bus 128)                 ; }  g-integers whose indices are interleaved,
                      (:nat b-bus 128)                 ; }  27 to 414 -- see below
                      (:rev (:seq (:nat c-bus 64)      ; } 
                                  (:skip 64))))   ; }
                (:rev (:nat fixup-bits 4))       ; g-integer with indices 420-415
                ))
})

<p>This is good because</p>

<ul>

<li>you don't have to think about sign bits and do a bunch of stupid arithmetic
to figure out the next free index, and</li>

<li>you can painlessly extend the bindings when you want to add a new variable
without having to update a bunch of indices.</li>

</ul>

<p>Auto-bindings are more limited than shape-specs.  Except for the special
@(':mix') command, you can only write:</p>

@({
    (:bool var)  -- expands to a g-boolean shape-specifier
    (:int var n) -- expands to a g-integer with n bits (signed 2's complement)
    (:nat var n) -- equivalent to (:int var (+ 1 n))
    (:skip n)    -- takes up space in a :mix, but doesn't generate bindings.
})

<p>The @(':rev') command reverses the order of the bits produced by directives inside it.</p>

<p>The @(':mix') command interleaves the bits of the elements inside it.
Currently we only allow mix to contain elements that are all the same size.</p>

<p>The @(':seq') and @(':mix') commands can be nested to produce complicated
interleavings.</p>

<p>The @(':skip') command can be used to pad out a @(':mix') command so as to
interleave a shorter variable with part of a longer variable.  E.g.:</p>
@({
 (:mix (:int a 7)
       (:seq (:int b 4) (:skip 3)))
 })
<p>produces</p>
@({
 ((A (:G-INTEGER 0 2 4 6 8 9 10))
  (B (:G-INTEGER 1 3 5 7)))
 })
<p>That is, the first part of @('a') is mixed with @('b') but once the bits of
@('b') run out, the rest of the bits of @('a') are simply in sequence.</p>
")

(defxdoc flex-bindings
  :parents (reference shape-specs)
  :short "Shape specifiers for @(':g-bindings'), more flexible than @(see auto-bindings)."
  :long "<p>The @('flex-bindings') function lets you create somewhat more
complicated @(see shape-specs) than is possible with @(see auto-bindings).  We
assume familiarity with @(see auto-bindings) in this documentation.  The
specific feature @('flex-bindings') offers that auto-bindings does not is the
ability to split an integer variable into segments and generate indices for
each segment independently.</p>

@({
 (def-gl-thm foo
   ...
   :g-bindings (flex-bindings                          ; expands to:
                 ;; auto-bindings list -- generates indices
                 ((:int a1 10)
                  (:rev (:mix (:int a2 13)
                              (:int b1 13)))
                  (:int b2 10))
                 :arrange         ;; generate shape spec bindings from the indices
                 ((:int a a1 a2)  ;; a is a g-integer, indices are a1's appended to a2's
                  (:int b b1 b2)))) 
})

<p>The first argument is just a list of auto-bindings (though the syntax
differs trivially in that flex-bindings takes them in a single argument whereas
@(see auto-bindings) uses @('&rest args')).  They are used to generate indices,
but not the actual g-bindings.  We generate from these a mapping from each
variable name to its list of indices.</p>

<p>The @(':arrange') argument, if provided, must be a list consisting of the
following sorts of forms: </p>

<ul>
<li>@('(:int a b c ...)') means generate an integer shape-spec binding for
variable @('a'), consisting of the appended indices of @('b'), @('c'), etc.,
from the auto-bindings form.</li>
<li>@('(:int a)') means generate an integer shape-spec binding for variable
@('a') using the indices of @('a') from the auto-bindings form.</li>
<li>@('(:bool a)') means generate a Boolean binding for variable @('a'),
using the index of @('a') from the auto-bindings form.</li>
<li>@('(:bool a b)') means generate a Boolean binding for variable @('a'),
using the index of @('b') from the auto-bindings form.</li>
</ul>

<p>If the @(':arrange') argument is not provided, @(see flex-bindings) acts
just like @(see auto-bindings) -- it generates an entry for each variable
mentioned in the auto-bindings.</p>")

;; throw-away versions of common functions
(defun ab-sum (x)
  (if (atom x)
      0
    (+ (car x) (ab-sum (cdr x)))))

(defun ab-all-equal (x val)
  (if (atom x)
      t
    (and (equal (car x) val)
         (ab-all-equal (cdr x) val))))

(mutual-recursion
 ;; takes a translated auto-bind form
 (defun auto-bind-len (x)
   (case (first x)
     (:bool 1)
     (:int (third x))
     (:rev (auto-bind-len (cadr x)))
     (:skip (second x))
     (t   (ab-sum (auto-bind-len-list (cdr x))))))
 (defun auto-bind-len-list (x)
   (if (atom x)
       nil
     (cons (auto-bind-len (car x))
           (auto-bind-len-list (cdr x))))))
     

(mutual-recursion
 (defun auto-bind-xlate (x inside-mix-p)
   ;; Syntax check that X is (:nat ...), (:int ...), or (:bool ...)
   ;; Converts (:nat ...) into (:int ...) with extra var.
   ;; Converts (:bool var) into (:bool var 1).
   (if (not (true-listp x))
       (er hard? 'auto-bind-xlate "Auto-binding not even a true-listp: ~x0" x)
     (case (first x)
       (:bool
        (cond (inside-mix-p
               (er hard? 'auto-bind-xlate "Auto-bindings of :bool aren't allowed directly inside mix: ~x0" x))
              ((and (= (len x) 2)
                    (acl2::legal-variablep (second x)))
               (list :bool (second x) 1))
              (t
               (er hard? 'auto-bind-xlate "Auto-binding is invalid: ~x0" x))))
       ((:nat :int)
        (if (and (= (len x) 3)
                 (acl2::legal-variablep (second x))
                 (natp (third x)))
            (list :int (second x) (if (eq (first x) :nat)
                                      (+ 1 (third x))
                                    (third x)))
          (er hard? 'auto-bind-xlate "Auto-binding is invalid: ~x0" x)))
       (:mix (b* (((unless (<= 3 (len x)))
                   (er hard? "Auto-binding is invalid: mix with too few elements: ~x0" x))
                  (elems (auto-bind-xlate-list (cdr x) t))
                  (lens (auto-bind-len-list elems))
                  ((unless (ab-all-equal (cdr lens) (car lens)))
                   (er hard? 'auto-bind-xlate
                       "Lengths inside :mix must agree: ~x0 has lengths ~x1"
                       elems lens)))
               (cons :mix elems)))
       (:seq (cons :seq (auto-bind-xlate-list (cdr x) nil)))
       (:rev (cond ((= (len x) 2)
                    (list :rev (auto-bind-xlate (cadr x) inside-mix-p)))
                   (t (er hard? 'auto-bind-xlate "Auto-binding is invalid: ~x0" x))))
       (:skip (if (and (= (len x) 2)
                       (natp (second x)))
                  x
                (er hard? 'auto-bind-xlate "Auto-binding is invalid: ~x0" x)))
       (otherwise
        (er hard? 'auto-bind-xlate "Auto-binding has unrecognized type: ~x0" x)))))

 (defun auto-bind-xlate-list (x inside-mix-p)
   (if (atom x)
       nil
     (cons (auto-bind-xlate (car x) inside-mix-p)
           (auto-bind-xlate-list (cdr x) inside-mix-p)))))

#||
(auto-bind-xlate '(:bool foo) nil)
(auto-bind-xlate '(:bool foo) t)
(auto-bind-xlate '(:nat bar 5) nil)
(auto-bind-xlate '(:int baz 5) nil)|
||#

;; (defun auto-bind-lens-ok (len x)
;;   ;; X has already been translated, so :NAT and :INT agree.
;;   ;; Make sure all have length LEN.
;;   (cond ((atom x)
;;          nil)
;;         ((equal len (third (car x)))
;;          (auto-bind-lens-ok len (cdr x)))
;;         (t
;;          (er hard? 'auto-bind-lens-ok
;;              "Lengths inside :mix must agree; expected length ~x0 but found ~x1 for ~x2."
;;              len (third (car x)) (car x)))))

;; (defun auto-bind-xlate-list (x inside-mix-p)
;;   ;; Expand out (:nat ...) into (:int ...), make sure all uses of :mix are okay.
;;   (cond ((atom x)
;;          (if (null x)
;;              nil
;;            (cw "Warning: weird final cdr of auto-bindings: ~x0.~%" x)))
;;         ((and (consp (car x))
;;               (eq (caar x) :mix))
;;          (cond (inside-mix-p
;;                 (er hard? 'auto-bind-xlate-list "Nested :mix commands are not supported."))
;;                ((not (cdar x))
;;                 (progn$
;;                  (cw "Warning: ignoring empty :mix in auto-bindings~%")
;;                  (auto-bind-xlate-list (cdr x) inside-mix-p)))
;;                (t
;;                 (let ((x-guts (auto-bind-xlate-list (cdar x) t)))
;;                   (progn$
;;                    (auto-bind-lens-ok (third (car x-guts)) (cdr x-guts))
;;                    (cons (cons :mix x-guts)
;;                          (auto-bind-xlate-list (cdr x) inside-mix-p)))))))
;;         (t
;;          (cons (auto-bind-xlate (car x) inside-mix-p)
;;                (auto-bind-xlate-list (cdr x) inside-mix-p)))))

#||
(auto-bind-xlate-list
 '((:bool foo)
   (:int a 6)
   (:nat b 5)
   (:mix (:int x 3)
         (:nat y 2))
   (:bool eep))
 nil)
||#

(mutual-recursion
 (defun auto-bind-generate (x free-idx by)
   ;; X is a translated auto-bind entry, i.e., a bool or int with its length available
   ;; Returns a singleton LIST of bindings so it can be appended (to make :mix easy)
   (case (car x)
     ((:bool :int)
      (b* (((list type var len) x))
        (list (cons var (if (eq type :bool)
                            (list free-idx)
                          (numlist free-idx by len))))))
     (:rev (let ((len (auto-bind-len (cadr x))))
             (auto-bind-generate (cadr x) (+ free-idx (* by (1- len))) (- by))))
     (:mix (auto-bind-generate-mix
            (cdr x) ;; entries
            free-idx ;; starting index
            by ;; how much to increment the starting index of each entry
            (* by (len (cdr x))))) ;; how much to increment within each entry
     (:seq (auto-bind-generate-seq
            (cdr x) free-idx by))
     (:skip nil)
     (otherwise
      (er hard? 'auto-bind-generate "Should never happen: not translated: ~x0" x))))

 (defun auto-bind-generate-mix (x free-idx interleave-by inner-by)
   (if (atom x)
       nil
     (append (auto-bind-generate (car x) free-idx inner-by)
             (auto-bind-generate-mix (cdr x) (+ free-idx interleave-by) interleave-by inner-by))))

 (defun auto-bind-generate-seq (x free-idx by)
   (if (atom x)
       nil
     (append (auto-bind-generate (car x) free-idx by)
             (auto-bind-generate-seq (cdr x)
                                     (+ (* by (auto-bind-len (car x))) free-idx)
                                     by)))))

(mutual-recursion
 (defun auto-bind-skips (x free-idx by)
   ;; Returns a list of skipped indices.
   (case (car x)
     ((:bool :int) nil)
     (:rev (let ((len (auto-bind-len (cadr x))))
             (auto-bind-skips (cadr x) (+ free-idx (* by (1- len))) (- by))))
     (:mix (auto-bind-skips-mix
            (cdr x) ;; entries
            free-idx ;; starting index
            by ;; how much to increment the starting index of each entry
            (* by (len (cdr x))))) ;; how much to increment within each entry
     (:seq (auto-bind-skips-seq
            (cdr x) free-idx by))
     (:skip (numlist free-idx by (cadr x)))
     (otherwise
      (er hard? 'auto-bind-generate "Should never happen: not translated: ~x0" x))))

 (defun auto-bind-skips-mix (x free-idx interleave-by inner-by)
   (if (atom x)
       nil
     (append (auto-bind-skips (car x) free-idx inner-by)
             (auto-bind-skips-mix (cdr x) (+ free-idx interleave-by) interleave-by inner-by))))

 (defun auto-bind-skips-seq (x free-idx by)
   (if (atom x)
       nil
     (append (auto-bind-skips (car x) free-idx by)
             (auto-bind-skips-seq (cdr x)
                                  (+ (* by (auto-bind-len (car x))) free-idx)
                                  by)))))


#||
(auto-bind-generate '(:int a 5) 0 2)
(auto-bind-generate '(:bool b 1) 0 1)
(auto-bind-generate 
 '(:mix
   (:int a 10)
   (:rev (:seq
          (:int b 6)
          (:rev (:int c 3))
          (:bool d 1))))
 0 1)
          
  
(auto-bind-generate-mix '((:int a 5) (:int b 5) (:int c 5)) 0 1 3)


(auto-bind-generate
 '(:mix (:int a 20)
        (:seq (:skip 4) (:int b 13) (:skip 3)))
 0 1)

(auto-bind-skips
 '(:mix (:int a 20)
        (:seq (:skip 4) (:int b 13) (:skip 3)))
 0 1)
        
||#

(defun auto-bind-index-map (n skiptable len offset acc)
  (if (mbe :logic (zp (- (nfix len) (nfix n)))
           :exec (eql n len))
      acc
    (if (hons-get n skiptable)
        (auto-bind-index-map (1+ (lnfix n)) skiptable len (1+ offset) acc)
      (auto-bind-index-map (1+ (lnfix n)) skiptable len offset
                           (hons-acons n (- n offset) acc)))))


      
(defun auto-bind-remap-indices-list (x indexmap)
  (b* (((when (atom x)) nil)
       (look (hons-get (car x) indexmap))
       ((unless look)
        (er hard? 'auto-bind-remap-index-list
            "Auto-bindings programming error: skipped index is present in auto-bindings")))
    (cons (cdr look)
          (auto-bind-remap-indices-list (cdr x) indexmap))))

(defun auto-bind-remap-indices-table (x indexmap)
  (if (atom x)
      nil
    (cons (cons (caar x) (auto-bind-remap-indices-list (cdar x) indexmap))
          (auto-bind-remap-indices-table (cdr x) indexmap))))


       
    




#||
(auto-bind-generate-seq '((:BOOL FOO 1)
                  (:INT A 6)
                  (:INT B 6)
                  (:MIX (:INT X 3) (:INT Y 3))
                  (:BOOL EEP 1))
                0 1)

||#

(defun flex-bindings-append-auto-vars (vars auto-alist)
  (if (atom vars)
      nil
    (append (b* ((auto-look (assoc (car vars) auto-alist))
                 ((unless auto-look)
                  (er hard? 'flex-bindings-arrange
                      "Missing auto-binding for ~x0" (car vars))))
              (cdr auto-look))
            (flex-bindings-append-auto-vars (cdr vars) auto-alist))))

(defun flex-bindings-arrange1 (x auto-alist)
  (b* (((when (atom x))
        (er hard? 'flex-bindings-arrange
                       "Invalid arrange-list entry: ~x0" x))
       ((cons key args) x)
       ((unless (and (consp args)
                     (symbol-listp args)
                     (not (member nil args))))
        (er hard? 'flex-bindings-arrange
                       "Invalid arrange-list entry: ~x0 -- args must be a ~
                        nonempty list of nonnil symbols" 
                       x)))
    (case key
      (:bool (b* ((len (len args))
                  ((unless (or (eql len 1) (eql len 2)))
                   (er hard? 'flex-bindings-arrange
                       "Invalid arrange-list entry: ~x0" x))
                  (varname (first args))
                  (autoname (if (eql len 2) (second args) (first args)))
                  (auto-look (assoc autoname auto-alist))
                  ((unless auto-look)
                   (er hard? 'flex-bindings-arrange
                       "Missing auto-binding for ~x0" autoname))
                  (indices (cdr auto-look))
                  ((unless (eql (len indices) 1))
                   (er hard? 'flex-bindings-arrange
                       "Boolean ~x0 assigned to wide auto-binding variable ~x1" varname autoname)))
               (list varname (g-boolean (car indices)))))
      (:int  (b* ((len (len args))
                  (varname (car args))
                  (auto-vars (if (eql len 1) args (cdr args))))
               (list varname (g-integer (flex-bindings-append-auto-vars auto-vars auto-alist)))))
      (otherwise (er hard? 'flex-bindings-arrange
                     "Invalid arrange-list entry: ~x0 -- must begin with :bool or :int.")))))
                  

(defun flex-bindings-arrange (arrange-list auto-alist)
  (if (atom arrange-list)
      nil
    (cons (flex-bindings-arrange1 (car arrange-list) auto-alist)
          (flex-bindings-arrange (cdr arrange-list) auto-alist))))

(mutual-recursion
 (defun auto-bindings-collect-arrange (x)
   (case (car x)
     ((:bool :int)
      (b* (((list type var) x))
        (list (list type var))))
     (:skip nil)
     (otherwise (auto-bindings-list-collect-arrange (cdr x)))))
 (defun auto-bindings-list-collect-arrange (x)
   (if (atom x)
       nil
     (append (auto-bindings-collect-arrange (car x))
             (auto-bindings-list-collect-arrange (cdr x))))))


(defun flex-bindings-fn (auto-bindings arrange-list start)
  ;; Auto-bindings are a list (implicitly :seq) of (untranslated)
  ;; auto-bindings.  They are used to generate the indices, but not the actual
  ;; g-bindings, i.e. we don't care whether something is (:bool x) or (:int x
  ;; 1).  We generate from these an alist mapping each variable name to its
  ;; list of indices.   Arrange is a list contiaining the following forms:
  ;; (:bool a)       --> generate `(a ,(g-boolean (cadr (assoc 'a auto-binding-alist))))
  ;; (:bool a b)     --> generate `(a ,(g-boolean (cadr (assoc 'b auto-binding-alist))))
  ;; (:int a)        --> generate `(a ,(g-integer (cdr (assoc 'a auto-binding-alist))))
  ;; (:int a b)      --> generate `(a ,(g-integer (cdr (assoc 'b auto-binding-alist))))
  ;; (:int a b c d)  --> generate `(a ,(g-integer (append (cdr (assoc 'b auto-binding-alist))
  ;;                                                     (cdr (assoc 'c auto-binding-alist))
  ;;                                                     (cdr (assoc 'd auto-binding-alist)))))
  ;; This last form is the point of the whole exercise -- to allow shape-spec
  ;; variables to be composed of multiple slices that are each placed
  ;; independently in the index ordering.
  (b* ((xlated-bindings (auto-bind-xlate-list auto-bindings nil))
       (auto-alist (auto-bind-generate-seq xlated-bindings start 1))
       (skips (auto-bind-skips-seq xlated-bindings start 1))
       (skiptable (make-fast-alist (pairlis$ skips nil)))
       (indexmap (auto-bind-index-map 0 skiptable
                                      (Ab-sum (auto-bind-len-list xlated-bindings))
                                      0 nil))
       (auto-alist-remapped (auto-bind-remap-indices-table auto-alist indexmap))
       (arrange-list (or arrange-list (auto-bindings-list-collect-arrange xlated-bindings))))
    (flex-bindings-arrange arrange-list auto-alist-remapped)))

(defmacro flex-bindings (auto-bindings &key arrange (start '0))
  `(flex-bindings-fn ',auto-bindings ',arrange ,start))

(defun flex-param-bindings (in-alist)
  ;; In-alist maps a parameter binding to an input list for flex-bindings, e.g. auto-bindings :arrange arrange.
  ;; Returns a full param-bindings alist, flex-bindings resolved.
  (b* (((when (atom in-alist)) nil)
       (case1 (car in-alist))
       ((unless (and (true-listp case1)
                     (or (eql (len case1) 2)
                         (and (eql (len case1) 4)
                              (eq (nth 2 case1) :arrange)))))
        (er hard? 'flex-param-bindings "Unsupported entry in flex-param-bindings: ~x0" case1))
       ((list params auto-bindings ?arrange-keyword arrange) case1))
    (cons (list params (flex-bindings-fn auto-bindings arrange 0))
          (flex-param-bindings (cdr in-alist)))))
    

       


(defun auto-bindings-fn (x)
  (flex-bindings-fn x nil 0))

(defmacro auto-bindings (&rest args)
  `(auto-bindings-fn ',args))


#||
(auto-bindings (:nat opcode 8)             ; g-integer with indices 0-8
               (:int multiplier 16)        ; g-integer with indices 9-24
               (:bool enable)              ; g-boolean with index 25
               (:mix (:nat a-bus 128)      ; }  g-integers whose indicies
                     (:nat b-bus 128)      ; }  are interleaved, 26 to 412
                     (:nat c-bus 128))     ; }
               (:nat fixup-bits 4)         ; g-integer with indices 413-417
               )


(auto-bindings (:mix (:nat foo 20)
                     (:seq (:skip 7) (:nat bar 9) (:skip 4))))

(auto-bindings                          ; expands to:
                (:nat opcode 8)                        ; g-integer with indices 0-8
                (:int multiplier 16)                   ; g-integer with indices 9-24
                (:bool enable)                         ; g-boolean with index 25
                (:mix (:nat a-bus 128)                 ; }  g-integers whose indices are interleaved,
                      (:nat b-bus 128)                 ; }  27 to 412 -- see below
                      (:rev (:seq (:nat c-bus 64)      ; } 
                                  (:nat dummy 63))))   ; }
                (:rev (:nat fixup-bits 4))       ; g-integer with indices 417-413
                )

(flex-bindings ((:int daz 1)
                (:int ftz 1)
                (:int rc 2)
                (:int a-sign 1)
                (:int b-sign 1)
                (:mix
                 (:int a-exp 8)
                 (:int b-exp 8))
                (:rev (:seq
                       (:int a-nonoverlap 10)
                       (:mix (:int a-overlap 13)
                        (:int b-overlap 13))
                       (:int b-nonoverlap 10)))
                (:int masks 6)
                (:int flags 6)
                (:nat a-upper 96)
                (:nat b-upper 96)
                (:int mxcsr-msb 1))
               :arrange
               ((:int mxcsr flags daz masks rc ftz mxcsr-msb)
                (:int a a-nonoverlap a-overlap a-exp a-sign a-upper)
                (:int b b-overlap b-nonoverlap b-exp b-sign b-upper)))

||#
