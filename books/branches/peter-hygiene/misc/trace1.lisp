; The following was originally part of ACL2 Version 3.4.  Peter Dillinger
; wanted a different version of trace*, and the easiest way to provide that has
; appeared to be to separate the implementation of trace* into a book, which
; can be loaded or not as one chooses.

(in-package "ACL2")

(defun trace*-modify1 (ctx trace-spec)
  (cond ((symbolp trace-spec)
         (list trace-spec
               :entry `(cons ',trace-spec arglist)
               :exit `(cons ',trace-spec values)))
        ((and (consp trace-spec)
              (symbolp (car trace-spec))
              (keyword-value-listp (cdr trace-spec)))
         (if (or (assoc-keyword :entry (cdr trace-spec))
                 (assoc-keyword :exit (cdr trace-spec)))
             trace-spec
           (let ((fn (car trace-spec)))
             (list* fn
                    :entry `(cons ',fn arglist)
                    :exit `(cons ',fn values)
                    (cdr trace-spec)))))
        (t (er hard ctx
               *illegal-trace-spec-fmt-string*
               trace-spec))))

(defun trace*-modify (ctx trace-specs)
  (cond ((endp trace-specs)
         nil)
        (t (cons (trace*-modify1 ctx (car trace-specs))
                 (trace*-modify ctx (cdr trace-specs))))))

(defmacro trace* (&rest trace-specs)

  ":Doc-Section Trace

  trace function evaluations~/

  ~c[Trace*] is a minor variant of ~ilc[trace$], the ACL2 tracing utility.
  ~l[trace$] for detailed documentation.

  The only difference between ~c[trace*] and ~c[trace$] is that ~c[trace*]
  provides perhaps more pleasant output, as follows.  If a function is traced
  without option ~c[:entry] or ~c[:exit], then ~c[trace*] avoids using the name
  of the so-called ``*1* function'' (also known as ``executable-counterpart
  function'' or ``logic function'').

  The log below illustrates the difference when using
  ~c[:set-guard-checking :none], which restricts execution to *1* functions.
  Here we assume the following definition.
  ~bv[]
  (defun fact (n)
    (if (zp n)
        1
      (* n (fact (1- n)))))
  ~ev[]
  And here is the log promised above, first showing ~c[trace$] and then the
  (prettier output from) ~c[trace*].
  ~bv[]
  ACL2 >(trace$ fact)
   ((FACT))
  ACL2 >(fact 3)
  1> (ACL2_*1*_ACL2::FACT 3)
    2> (ACL2_*1*_ACL2::FACT 2)
      3> (ACL2_*1*_ACL2::FACT 1)
        4> (ACL2_*1*_ACL2::FACT 0)
        <4 (ACL2_*1*_ACL2::FACT 1)
      <3 (ACL2_*1*_ACL2::FACT 1)
    <2 (ACL2_*1*_ACL2::FACT 2)
  <1 (ACL2_*1*_ACL2::FACT 6)
  6
  ACL2 >(trace* fact)
   ((FACT :ENTRY (CONS 'FACT ARGLIST)
          :EXIT (CONS 'FACT VALUES)))
  ACL2 >(fact 3)
  1> (FACT 3)
    2> (FACT 2)
      3> (FACT 1)
        4> (FACT 0)
        <4 (FACT 1)
      <3 (FACT 1)
    <2 (FACT 2)
  <1 (FACT 6)
  6
  ACL2 >
  ~ev[]~/~/"

  `(trace$ ,@(trace*-modify 'trace* trace-specs)))
