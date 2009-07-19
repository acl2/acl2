; Enhancement of defpun to allow more than one tail-recursive call.
; Matt Kaufmann
; August 2007

; Notes:

; The implementation could likely be made more efficient by using if* instead
; of if and having rewrite rules to resolve if* when the test is known true or
; known false.  This approach could avoid explosion during clausification
; following the :use hint.

; Example:

#||

(defstub dest (x) t)

(defstobj st fld)

(defp foo (x st)
  (let ((y (foo (dest (car x)) st)))
    (if (consp (car x))
        y
      (if (consp x)
          (foo (dest x) st)
        (cons x (fld st)))))
  :rule-classes nil)

||#

(in-package "ACL2")

(include-book "defpun")

(defun defpun-add-test (test tests-and-stuff-lst)
  (declare (xargs
            :guard
            (and (alistp tests-and-stuff-lst)
                 (true-list-listp (strip-cars tests-and-stuff-lst)))))
  (if (endp tests-and-stuff-lst)
      nil
    (let ((tests (caar tests-and-stuff-lst))
          (call (cdar tests-and-stuff-lst)))
      (cons (cons (cons test tests)
                  call)
            (defpun-add-test test (cdr tests-and-stuff-lst))))))

(verify-termination dumb-negate-lit)

(defun defpun-calls-tests-and-args-lst (fn term)
  (case-match term
    ((!fn . args)
     (list (cons nil args)))
    (('if test tbr fbr)
     (let ((tbr-tests-and-args-lst
            (defpun-calls-tests-and-args-lst fn tbr))
           (fbr-tests-and-args-lst
            (defpun-calls-tests-and-args-lst fn fbr)))
       (append (defpun-add-test
                 test
                 tbr-tests-and-args-lst)
               (defpun-add-test
                 (dumb-negate-lit test)
                 fbr-tests-and-args-lst))))
    (& nil)))

(defun defpun-tests-and-base-lst (fn term)
  (case-match term
    ((!fn . &)
     nil)
    (('if test tbr fbr)
     (let ((tbr-base
            (defpun-tests-and-base-lst fn tbr))
           (fbr-base
            (defpun-tests-and-base-lst fn fbr)))
       (append (defpun-add-test
                 test
                 tbr-base)
               (defpun-add-test
                 (dumb-negate-lit test)
                 fbr-base))))
    (& (list (cons nil term)))))

(defun map-conjoin (lst)
  (declare (xargs :guard (true-list-listp lst)))
  (if (endp lst)
      nil
    (cons (conjoin (car lst))
          (map-conjoin (cdr lst)))))

(defun defpun-disjoin-tests (tests-and-args-lst)
  (declare (xargs :guard (and (alistp tests-and-args-lst)
                              (true-list-listp
                               (strip-cars tests-and-args-lst)))))
  (let ((tests-lst (strip-cars tests-and-args-lst)))
    (disjoin (map-conjoin tests-lst))))

; (verify-termination quote-listp (declare (xargs :verify-guards t)))
; (verify-termination cons-term2 (declare (xargs :verify-guards t))) ; fails
; (verify-termination cons-term (declare (xargs :verify-guards t)))

(program)

(defun defpun-make-nth-arg (tests-and-args-lst n)
  (declare (xargs :guard (and (alistp tests-and-args-lst)
                              (true-list-listp
                               (strip-cars tests-and-args-lst)))))
  (if (endp (cdr tests-and-args-lst))
      (nth n (cdar tests-and-args-lst))
    (fcons-term* 'if
                 (conjoin (caar tests-and-args-lst))
                 (nth n (cdar tests-and-args-lst))
                 (defpun-make-nth-arg (cdr tests-and-args-lst) n))))

(defun defpun-make-call (fn tests-and-args-lst n acc)
  (if (zp n)
      (cons-term fn acc)
    (let ((n (1- n)))
      (defpun-make-call
        fn
        tests-and-args-lst
        n
        (cons (defpun-make-nth-arg tests-and-args-lst n)
              acc)))))

(defun defpun-make-base (tests-and-base-lst)
  (if (endp (cdr tests-and-base-lst))
      (cdar tests-and-base-lst)
    (fcons-term* 'if
                 (conjoin (caar tests-and-base-lst))
                 (cdar tests-and-base-lst)
                 (defpun-make-base (cdr tests-and-base-lst)))))

(defmacro defp (g vars body &key (rule-classes ':definition))
  `(make-event
    (er-progn
     (defstub ,g ,vars t)
     (er-let*
      ((tbody0 (translate ',body t t nil '(defp . ,g) (w state) state)))
      (let* ((tbody (remove-lambdas tbody0))
             (tests-and-args-lst
              (defpun-calls-tests-and-args-lst ',g tbody))
             (call (defpun-make-call ',g tests-and-args-lst ,(length vars)
                     nil))
             (tests-and-base-lst
              (defpun-tests-and-base-lst ',g tbody))
             (base (defpun-make-base tests-and-base-lst))
             (test (defpun-disjoin-tests tests-and-base-lst))
             (new-body
              (untranslate (fcons-term* 'if test base call) nil (w state))))
        (if (ffnnamep ',g base)
            (mv (msg "Unable to process the suggested definition as tail ~
                      recursive.  Possible debug info: A problem call has ~
                      been collected into the base case:~|~%  ~x0"
                     (untranslate base nil (w state)))
                nil
                state)
          (value
           (list
            'encapsulate
            '((,g ,vars t))
            (list 'local (list 'defpun ',g ',vars new-body :rule-classes nil))
            (list 'defthm
                  ',(packn-pos (list g "$DEF") g)
                  (list 'equal
                        (cons ',g ',vars)
                        ',body)
                  :hints
                  '(("Goal"
                     :in-theory (theory 'minimal-theory)
                     :use ,(packn-pos (list g "-DEF") g)))
                  :rule-classes ',rule-classes)))))))))

