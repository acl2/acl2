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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>


(in-package "VL")

(include-book "scopestack")
(include-book "centaur/sv/svex/svex" :dir :system)
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable acl2::consp-under-iff-when-true-listp)))

(defxdoc elabindex
  :parents (elaborate)
  :short "A data structure for recording elaboration results, i.e., functions,
types, and parameters."
  :long "
<h3>Introduction</h3>
<p>One of the biggest difficulties in processing SystemVerilog is the
complicated dependencies among functions, parameters, and types.  There is no
way to unravel these dependencies so that we can (e.g.) resolve parameter
values first, then types, then function definitions: in fact, each of these can
depend on all the others.  So they must all be processed in one step, so that
if a parameter depends on a function definition, we can go and resolve that
function definition, which may depend on other parameters and types, before
coming back to the original parameter with the function's resolved definition.</p>

<p>The step that resolves all of these is called elaboration.  During
elaboration, we unparameterize modules and traverse the design in order to
resolve types and replace constant expressions with their values where
possible.  Elaboration is complicated by the fact that there is no set order
for dependencies; we must be able to go look up an arbitrary
parameter/function/type anywhere in the module and resolve it before
continuing.</p>

<p>This style of traversal is difficult for our applicative-style data
structures; when we go to a different part of the design, resolve something,
and come back to another part of the design, it is expensive to record the
result that we obtained in the design, especially since it has been
processed (e.g.) a scopestack.</p>

<p>An elabindex is our solution to this problem.  It is designed to allow us to
efficiently record and look up results while performing both treelike and
non-treelike traversals of the design.</p>")

(defoption vl-maybe-elabkey vl-elabkey)

(deftagsum vl-elabinfo
  (:function ((body  sv::svex)
              (ports vl-portdecllist)
              (type  vl-datatype)))
  (:type    ((type vl-datatype))
   :short "used for both typedefs and type parameters")
  (:param   ((type vl-datatype)
             (value-expr vl-expr)
             (value-sv   sv::svex)))
  :measure (two-nats-measure (acl2-count x) 0))

(fty::defalist vl-elabinfo-alist :key-type stringp :val-type vl-elabinfo
  :measure (two-nats-measure (acl2-count x) 0))

(defoption vl-maybe-elabinfo vl-elabinfo)

(deftagsum vl-elabkey
  (:package ((name stringp)) :hons t)
  (:item    ((name stringp)) :hons t)
  (:def     ((name stringp)) :hons t)
  :layout :tree)


(deftypes vl-elabscope
  
  (fty::defalist vl-elabscope-alist :key-type vl-elabkey :val-type vl-elabscope
    :measure (two-nats-measure (acl2-count x) 0))

  (defprod vl-elabscope
    ((subscopes vl-elabscope-alist)
     (members vl-elabinfo-alist))
    :measure (two-nats-measure (acl2-count x) 1)))


(defines vl-elabscope-clean
  (define vl-elabscope-alist-clean ((x vl-elabscope-alist-p)
                                    (acc vl-elabscope-alist-p))
    :returns (res vl-elabscope-alist-p)
    :measure (vl-elabscope-alist-count x)
    :verify-guards nil
    (b* ((x (vl-elabscope-alist-fix x))
         (acc (vl-elabscope-alist-fix acc))
         ((when (atom x)) acc)
         ((cons key val) (car x))
         ((when (hons-get key acc))
          (vl-elabscope-alist-clean (cdr x) acc))
         (val (vl-elabscope-clean val)))
      (vl-elabscope-alist-clean (cdr x) (hons-acons key val acc))))
  (define vl-elabscope-clean ((x vl-elabscope-p))
    :returns (res vl-elabscope-p)
    :measure (vl-elabscope-count x)
    (b* (((vl-elabscope x))
         (- (fast-alist-free x.members)
            (fast-alist-free x.subscopes))
         (members (fast-alist-clean x.members))
         (subscopes (vl-elabscope-alist-clean x.subscopes nil)))
      (change-vl-elabscope x :members members :subscopes subscopes)))
  ///
  (verify-guards vl-elabscope-alist-clean))

(defthm cdr-hons-assoc-equal-of-vl-elabscope-alist-p
  (implies (vl-elabscope-alist-p x)
           (iff (cdr (hons-assoc-equal k x))
                (hons-assoc-equal k x)))
  :hints(("Goal" :in-theory (enable vl-elabscope-alist-p)
          :induct (len x))))

(defthm cdr-hons-assoc-equal-of-vl-elabinfo-alist-p
  (implies (vl-elabinfo-alist-p x)
           (iff (cdr (hons-assoc-equal k x))
                (hons-assoc-equal k x)))
  :hints(("Goal" :in-theory (enable vl-elabinfo-alist-p)
          :induct (len x))))


(define vl-elabscope-subscope ((key vl-elabkey-p) (x vl-elabscope-p))
  :returns (subscope (iff (vl-elabscope-p subscope) subscope))
  (cdr (hons-get (vl-elabkey-fix key) (vl-elabscope->subscopes x))))

(define vl-elabscope-package-subscope ((name stringp) (x vl-elabscope-p))
  :returns (subscope (iff (vl-elabscope-p subscope) subscope))
  (vl-elabscope-subscope (vl-elabkey-package name) x))

(define vl-elabscope-def-subscope ((name stringp) (x vl-elabscope-p))
  :returns (subscope (iff (vl-elabscope-p subscope) subscope))
  (vl-elabscope-subscope (vl-elabkey-def name) x))

(define vl-elabscope-item-subscope ((name stringp) (x vl-elabscope-p))
  :returns (subscope (iff (vl-elabscope-p subscope) subscope))
  (vl-elabscope-subscope (vl-elabkey-item name) x))

(define vl-elabscope-item-info ((name stringp) (x vl-elabscope-p))
  :returns (info (iff (vl-elabinfo-p info) info))
  (cdr (hons-get (string-fix name) (vl-elabscope->members x))))


(define vl-elabscope-update-subscope ((key vl-elabkey-p) (val vl-elabscope-p) (x vl-elabscope-p))
  :returns (new-x vl-elabscope-p)
  (change-vl-elabscope
   x
   :subscopes (hons-acons (vl-elabkey-fix key)
                          (vl-elabscope-fix val)
                          (vl-elabscope->subscopes x))))

(define vl-elabscope-update-subscope? ((key vl-elabkey-p) (val vl-elabscope-p) (x vl-elabscope-p))
  :returns (new-x vl-elabscope-p)
  (if (hons-equal (vl-elabscope-subscope key x) (vl-elabscope-fix val))
      (vl-elabscope-fix x)
    (vl-elabscope-update-subscope key val x)))
  

(define vl-elabscope-update-package-subscope ((name stringp) (val vl-elabscope-p) (x vl-elabscope-p))
  :returns (new-x vl-elabscope-p)
  (vl-elabscope-update-subscope (vl-elabkey-package name) val x))



(define vl-elabscope-update-def-subscope ((name stringp) (val vl-elabscope-p) (x vl-elabscope-p))
  :returns (new-x vl-elabscope-p)
  (vl-elabscope-update-subscope (vl-elabkey-def name) val x))

(define vl-elabscope-update-item-subscope ((name stringp) (val vl-elabscope-p) (x vl-elabscope-p))
  :returns (new-x vl-elabscope-p)
  (vl-elabscope-update-subscope (vl-elabkey-item name) val x))

(define vl-elabscope-update-item-info ((name stringp) (val vl-elabinfo-p) (x vl-elabscope-p))
  :returns (new-x vl-elabscope-p)
  (change-vl-elabscope
   x
   :members (hons-acons (string-fix name)
                        (vl-elabinfo-fix val)
                        (vl-elabscope->members x))))




(fty::defalist vl-elabscope-stack :key-type vl-maybe-elabkey :val-type vl-elabscope)


(defstobj elabindex
  (ss :type (satisfies vl-scopestack-p) :initially nil)
  (scopes :type (satisfies vl-elabscope-stack-p) :initially nil)
  :renaming ((ss vl-elabindex->ss)
             (scopes vl-elabindex->scopes)
             (update-ss vl-elabindex-update-ss)
             (update-scopes vl-elabindex-update-scopes)))

(define vl-elabindex-pop-scope (&key (elabindex 'elabindex))
  (b* ((ss (vl-elabindex->ss elabindex))
       (new-ss (vl-scopestack-pop ss))
       (elabindex (vl-elabindex-update-ss new-ss elabindex))
       (scopes (vl-elabindex->scopes elabindex))
       ((when (< (len scopes) 2))
        (raise "Not enough scopes remaining to pop!~%")
        elabindex)
       ((list* (cons scope1key scope1) (cons scope2key scope2) rest) scopes)
       ((unless scope1key)
        (vl-elabindex-update-scopes (cdr scopes) elabindex))
       (scope2 (vl-elabscope-update-subscope? scope1key scope1 scope2)))
    (vl-elabindex-update-scopes (cons (cons scope2key scope2) rest) elabindex)))


(define vl-elabindex-update-item-info ((name stringp) (val vl-elabinfo-p)
                                       &key (elabindex 'elabindex))
  (b* ((scopes (vl-elabindex->scopes elabindex))
       ((when (atom scopes))
        (raise "No scope -- can't update item info!~%")
        elabindex)
       ((cons (cons scope1key scope1) rest) scopes)
       (scope1 (vl-elabscope-update-item-info name val scope1)))
    (vl-elabindex-update-scopes (cons (cons scope1key scope1) rest) elabindex)))

(define vl-elabindex-init ((x vl-design-p)
                           &key (elabindex 'elabindex))
  (b* ((elabindex (vl-elabindex-update-ss (vl-scopestack-init x) elabindex)))
    (vl-elabindex-update-scopes (list (cons nil (make-vl-elabscope))) elabindex)))

(local (in-theory (disable nth)))

  
(define vl-elabindex-push-scope ((scope vl-scope-p)
                                 elabindex)
  (b* ((name (vl-scope->name scope))
       (type (vl-scope->scopetype scope))
       (key (and name
                 (case type
                   ((:vl-module :vl-interface)
                    (vl-elabkey-def name))
                   ((:vl-fundecl :vl-taskdecl :vl-genblock :vl-genarrayblock)
                    (vl-elabkey-item name))
                   (:vl-package (vl-elabkey-package name))
                   (otherwise nil))))
       (elabscopes (vl-elabindex->scopes elabindex))
       ((when (atom elabscopes))
        (raise "No outer scope -- can't push scope!")
        elabindex)
       (curr-elabscope (cdar elabscopes))
       (new-elabscope (or (and key
                               (vl-elabscope-subscope key curr-elabscope))
                          (make-vl-elabscope)))
       (elabindex
        (vl-elabindex-update-ss
         (vl-scopestack-push scope (vl-elabindex->ss elabindex))
         elabindex)))
    (vl-elabindex-update-scopes (cons (cons key new-elabscope) elabscopes) elabindex)))



        
        
      
                 
                 
    
    
  
