#|$ACL2s-Preamble$;
;;Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "DEFDATA")

; Put everything together

(include-book "base")


(include-book "sig" :ttags :all)


(include-book "xdoc/top" :dir :system)

(defxdoc defdata
  :parents (acl2::acl2-sedan acl2::macro-libraries acl2::cgen)
  :short "A Data Definition Framework"
  :long
"
<h3>Introduction</h3>

<p>
The defdata framework enables the convenient specification of
data types in ACL2s, the ACL2 Sedan.  The framework concisely
supports common data definition patterns, e.g., list types, map
types, enumerated types, record types, and mutually-recursive
types. It also provides support for polymorphic functions and 
tight integration with Tau.
</p>

<p>
The data definition framework is a key component of
counterexample generation support in ACL2s, but can be
independently used in ACL2, and is available as a community book.
</p>

<p>
The defdata framework maintains both a predicative
characterization, via a predicate recognizing elements of the
datatype, and an enumerative characterization, via a function
that can be used to enumerate all the elements of the
datatype. ACL2s picks out the recognizers in a conjecture and can
use the datatype enumerators to generate random elements of the
datatype. This is a key part of counterexample generation in
ACL2s.
</p>

<p>
The defdata framework also allows us to increase the amount of
automation ACL2s provides for reasoning about data definitions.
For example, our framework generates useful theorems, with
appropriate rule-classes, for list types; it generates accessor
and constructor functions for records with a suitable theory for
reasoning about compositions of these functions; it generates
theorems that characterize the type relations such as inclusion
and exclusion; and it generates events that support polymorphic
type reasoning.
</p>

<p> The defdata framework is described in our ACL2 2014 paper (a link
to the paper appears later). Below, we provide some examples of its
use.</p>

<p>Note: If you are trying these examples in a package other than ACL2S,
then you might have to prefix the basic typenames i.e. acl2s::pos.</p>

<h3>Examples</h3>

<h4>Union and Product types</h4>
@({
  (defdata inode nat)
  
  (defdata file (cons inode string))
  (defdata er-file (oneof file nil))
  
  (defdata UPNest 
    (oneof (oneof (cons (oneof 11 7) pos-list) 'ok symbol-alist) 
           (cons symbol (complex integer -1))
           (oneof (oneof 42 (cons pos file) er-file) t 7/6)
           \"nice\"))
  
  (defdata loi (oneof nil (cons integer loi)))
})

<h4>Range types</h4>
@({
  (defdata cache-miss-ratio (range rational (0 < _ < 1)))
  
  (defdata big-unsigned-num (range integer ((expt 2 32) < _)))
})
<p> 
Macros are allowed and the meaning of the defdata body
is the given by its macroexpansion.
</p>
@({
  (defdata 3d-point (list rational rational rational))
})

<h4>Enum types</h4>
@({
  (defdata op-code (enum '(lw sw addi subi beqz jr)))
  
  (defun generate-instruction-opcodes (x)
    (if (eq x 'mips-risc-model)
        '(lw sw addi subi beqz jr)
      '()))
  
  (defdata op-code1 (enum (generate-instruction-opcodes 'mips-risc-model)))
})

<h4>List and Alist types</h4>
@({
  (defdata files (listof file))

  (defdata symb-alist (alistof symbol all))
})

<h4>Mutually-recursive types</h4>
@({
  (defdata 
    (dir (listof (cons string dir-entry)))
    (dir-entry (oneof file dir)))
  
  (defdata
    (sexpr (oneof symbol
                  (cons symbol sexpr-list)))
    (sexpr-list (oneof nil
                       (cons sexpr sexpr-list))))  
})

<h4>Record (Struct) types</h4>
@({
  (defdata reg-num (range integer (0 <= _ < 32)))
  (defdata immediate-range (range integer (0 <= _ < (expt 2 16))))
  
  (defdata inst (record (op  . op-code)
                        (rd  . reg-num)
                        (rs1 . reg-num)
                        (imm . immediate-range)))
})


<h4>Map (unique and sorted entries) types</h4>
@({
  (defdata p-addr (range integer (0 <= _ < (expt 2 32))))
  (defdata imem (map p-addr inst))
})

<h4>Using record and map types</h4>
@({
  (b* (;; pick a random imemory
         (I (nth-imem 4511))
         ;; fix a program counter value
         (pc 1)
         ;; get the instruction pointed to by pc
         (instr (mget pc I)) 
         ;; get immediate value field of instr
         (im (inst-imm instr))
         ;; set immediate value field and the pc entry 
         (I1 (mset pc (set-inst-imm (1+ im) instr) I))
         ;; alternative way of getting immediate value field
         (im2 (mget :imm (mget pc I1)))
         ((inst op rd rs1 ?imm) instr)
         )
    (equal (inst op rd rs1 (1- im2)) instr))
})

<h4>Custom types</h4>
@({
  (defun make-descending-addresses (n)
    (if (zp n)
      nil
      (cons (1- n) (make-descending-addresses (- n 1)))))
  
  (defun imem-custom-enum (n)
    (declare (xargs :mode :program))
    (let* ((m (nth-imem-builtin n))
           (vals (strip-cdrs m))
           (keys (make-descending-addresses (len m))))
      (pairlis$ keys vals)))
  
  (defun imem-customp (x)
    (or (null x)
        (and (consp x)
             (consp (car x))
             (imem-customp (cdr x))
             (instp (cdar x))
             (p-addrp (caar x))
             (or (and (null (cdr x))
                      (equal 0 (caar x)))
                 (> (caar x) (caadr x))))))
  
  (register-type imem-custom
                 :predicate imem-customp
                 :enumerator imem-custom-enum)
  
  
  (defdata-attach imem :test-enumerator imem-custom-enum)
})


<h4>Recursive record types (similar to ML datatype facility)</h4>
@({
  (defdata tree (oneof 'Leaf 
                       (node (val   . string)
                             (left  . tree)
                             (right . tree))))
})


<h4>Polymorphic Type Signatures</h4>
@({
  (sig binary-append ((listof :a) (listof :a)) => (listof :a))
  (sig nthcdr (nat (listof :a)) => (listof :a))
  (sig nth (nat (listof :a)) => :a 
       :satisfies (< x1 (len x2)))
  ;; xi corresponds to the ith type appearing in the sig form. For example,
  ;; x1 corresponds to nat and x2 to (listof :a) 
})

<h4>Registering a data constructor</h4>
@({
  (defun acons-caar (x)  (caar x))
  (defun acons-cdar (x)  (cdar x))
  (defun acons-cdr (x)  (cdr x))
  
  (defthm acons-acl2-count-lemma
    (equal (acl2-count (acons x1 x2 x3))
           (+ 2 (acl2-count x1) (acl2-count x2) (acl2-count x3))))
  
  (register-data-constructor (aconsp acons)
                             ((allp acons-caar) (allp acons-cdar) (allp acons-cdr))
                             :rule-classes (:rewrite)
                             :verbose t)
})

<h4>Registering a type</h4>
@({
  (defun nth-even-builtin (n) 
    (declare (xargs :guard (natp n)))
    (* 2 (nth-integer n)))
  
  (register-type even 
                 :predicate evenp 
                 :enumerator nth-even-builtin)
})

<h4>Registering user-defined combinators</h4>
@({
  (register-user-combinator alistof 
   :arity 2 :verbose t
   :aliases (acl2::alistof)
   :expansion (lambda (_name _args) `(OR nil (acons ,(car _args) ,(cadr _args) ,_name)))
   :syntax-restriction-fn proper-symbol-listp
   :polymorphic-type-form (alistof :a :b)
   :post-pred-hook-fns (user-alistof-theory-events))
})

<h3>Debugging</h3>
<p>
To debug a failed defdata form, you can proceed in multiple ways:
<ul>
<li> At the session editor (or emacs prompt), submit/evaluate
     @(':trans1 (defdata ...)')
     And from the output, evaluate the form that says @('(defdata-events ...)').</li>
<li> Use keyword options @(':verbose t') and examine the ACL2 output.</li>
</ul>
</p>

<h3>More details</h3> 

<p> Although most constructs of the defdata language are
package-agnostic, some of the API functions/macros of the Defdata
framework (like <tt>sig</tt>) reside in the ACL2S package. Use
list (<tt>*acl2s-exports*</tt>) to import these symbols into your own
package.</p>

<p> For a comprehensive user guide and more details please refer to the following
<a href=\"http://arxiv.org/abs/1406.1557\">paper</a> </p>
"
)

(defxdoc register-type
  :parents (defdata acl2::cgen)
  :short "Register a name as a defdata type"
  :long
"
<h3>Example</h3>
@({
  (defun nth-odd-builtin (n) 
    (if (evenp n)
        (1+ n)
      (- n)))
  
  (register-type odd
                 :predicate oddp 
                 :enumerator nth-odd-builtin)
})

<h3>Introduction</h3>
<p>
A defdata type expression can either be a typename, a quoted constant or
a combinator or constructor expression. To serve as a typename, a symbol
should either have been defined using the @('defdata') macro, or
it should have been 
<i>registered</i> as a <i>defdata type</i> using the @('register-type')
macro.
</p>

<p>
As an example, after having <i>registered</i> @('odd') above, we can
now use @('odd') to define other @'(defdata') types, e.g., a list of
odd numbers: 
</p>
@({
  (defdata odds (listof odd))
})

<h4>General Form:</h4>
@({
(register-type name
               :predicate pred
               :enumerator enum
               [:enum/acc enum2]
               [:enum/test tenum]
               [:enum/test/acc tenum2]
               [:clique tnames]
               [:normalized-def nexp]
               [:prettyified-def pexp]
               ...)
})


Consider the above call of @('register-type'). We expect the following guards to be satisfied.
<ul>
<li><i>pred</i> is a monadic boolean-valued function.</li>
<li><i>enum, tenum</i> are 1-arity functions that take a natural number and return a value of the right type.</li>
<li><i>enum2, tenum2</i> are 2-arity functions that take a natural number and a random seed and return (mv value seed).</li>
<li> The rest of the options are for experts and are not yet documented. </li>
</ul>
"
)

(defxdoc register-data-constructor
  :parents (defdata)
  :short "Register a data constructor (to extend the defdata language)"
  :long
"
<h3>Introduction</h3>
<p>
You must be familiar with compound data types specified by @('defdata')
using @('cons'). Although @('cons') has a unique status in ACL2, it
is not natively available in the @('defdata') language unlike
built-in combinators such as @('oneof') and @('range'). In fact,
advanced users can introduce custom notions of product data by
using the @('register-data-constructor') macro, whose usage we show below.
</p>

<h3>Example</h3>
<p>
Consider the @('symbol-alist') type defined as @('(oneof nil (cons (cons symbol
all) symbol-alist))'). We could have registered @('acons') as a data
constructor, and alternatively defined @('symbol-alist') using @('acons')
instead of @('cons').
</p>
@({
  (defun aconsp (x)
    (and (consp x) (consp (car x))))
  
  (defun acons-caar (x)  (caar x))
  (defun acons-cdar (x)  (cdar x))
  (defun acons-cdr  (x)  (cdr x))
  
  (register-data-constructor (aconsp acons)
                             ((allp acons-caar) (allp acons-cdar) (allp acons-cdr)))
  
  (defdata symbol-alist (oneof nil (acons symbol all symbol-alist)))
})

<p>
In fact, this is how we setup the base environment in
\"defdata/base.lisp\": we use @('register-data-constructor') to
preregister all the primitive data constructors in ACL2. In
particular, the following (primitive) constructors are available to
build product types: @('cons'), @('intern$'), @('/') and @('complex').
</p>

<h3>General Form:</h3>
@({
  (register-data-constructor (recognizer constructor)
                             ((destructor-pred1 destructor1) ...)
                             [:proper bool]
                             [:hints hints]
                             [:rule-classes rule-classes])
})
"
)




(defxdoc sig 
  :parents (defdata acl2::macro-libraries)
  :short "Specify type signatures for polymorphic functions"
  :long
"
<h3>Examples:</h3>
@({
  (sig nthcdr (nat (listof :a)) => (listof :a))
  
  (sig binary-append ((listof :a) (listof :a)) => (listof :a))
  
  (sig nth (nat (listof :a)) => :a 
       :satisfies (< x1 (len x2))) 
  ;; xi corresponds to the ith type appearing in the sig form. For example,
  ;; x1 corresponds to nat and x2 to (listof :a) 

})



<h3>General Form:</h3>
@({
  (sig fun-name arg-types => return-type 
       [:satisfies hyp]
       [:hints hints]
       [:gen-rule-classes rule-classes]
       [:rule-classes rule-classes]
       [:verbose t])
})
<p>
where <i>arg-types</i> is a list of @('defdata') type expressions
and <i>return-type</i> is a @('defdata') type expression with the
added capability of referring to type variables, which in our
syntax are represented using keyword symbols @(':a, :b, :c, ...').
</p>

<p>
Note: @('sig') is currently limited to only 12 type variables.
Check @(':pe *allowed-type-vars*') to view them. We have never encountered
type signatures with more than 3 type variables, so we hope that this is
not a limitation in practice. There are several other limitations
we impose on @('sig'). If you would like more comprehensive
support, contact Pete and Harsh.
</p>

<p>
The following keyword arguments are supported by the @('sig') macro:
<ul>
<li> :satisfies -- specify additional dependent type hypotheses.</li>
<li> :hints -- @(see acl2::hints) option to the generic type signature.</li>
<li> :gen-rule-classes --  @(see acl2::rule-classes) option to the generic type signature.</li>  
<li> :rule-classes --  @(see acl2::rule-classes) option to the generated theorems.</li>  
<li> :verbose -- for debugging.</li>  
</ul>

</p>
"
)


(defxdoc register-user-combinator
  :parents (defdata)
  :short "Register a user-defined combinator (to add sugar to defdata language)"
  :long
"
<h3>Introduction</h3>

<p> User-defined combinators add syntactic sugar on top of the core
defdata language. In addition it is also possible to specify the
theory support for such a construct via the
<tt>:post-pred-hook-fns</tt> keyword option. (See alistof.lisp for
example usage).</p>

<h3>Example</h3>
Here is how we added <i>alistof</i> to the defdata language:
@({
  (register-user-combinator alistof 
   :arity 2 :verbose t
   :aliases (acl2::alistof)
   :expansion (lambda (_name _args) `(OR nil (acons ,(car _args) ,(cadr _args) ,_name)))
   :syntax-restriction-fn proper-symbol-listp
   :polymorphic-type-form (alistof :a :b)
   :post-pred-hook-fns (user-alistof-theory-events))
})

<h3>General Form:</h3>
@({
  (register-user-combinator combinator-name 
                            :arity num 
                            :expansion term 
                            [optional args])
})
"
)


(defxdoc defdata-attach
  :parents (defdata acl2::cgen)
  :short "Attach/modify metadata for a defdata type"
  :long
"
<h3>Examples:</h3>
@({
  (defdata-attach pos :enumerator nth-small-pos-testing)
  
  (defdata-attach imem :enum/acc imem-custom-enum2)
})

<h3>General Form:</h3>
@({
  (defdata-attach typename 
       [:enum/test enum-fn]
       [:equiv eq-rel]
       [:equiv-fixer eq-fix-fn]
       [:constraint ... ]
       [:sampling constant-list]
       [overridable metadata]
       )

}) 

<p> Defdata-attach can be used to attach custom test enumerators for
certain types. This provides a method to customize Cgen's test data
generation capability for certain scenarios.</p>

<p> (Advanced) Type refinement : User can attach rules that
specify (to Cgen) how to refine/expand a variable of this type when
certain additional constraints match (or subterm-match). For those who
are familar with dest-elim rules, the :rule field has a similar form.
For example: </p>

@({
(defdata-attach imemory
         :constraint (mget a x) ;x is the variable of this type
         :constraint-variable x
         :rule (implies (and (natp a) ;additional hyps
                             (instp x.a)
                             (imemoryp x1))
                        (equal x (mset a x.a x1))) ;refine/expand
         :meta-precondition (or (variablep a)
                                (fquotep a))
         :match-type :subterm-match)
})

<p> Warning: Other optional keyword arguments are currently
unsupported and the use of :override-ok can be unsound.</p>
"
)
