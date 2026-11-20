(in-package "ACL2")
(include-book "util")

; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

; Example 1: Joe & Robert -----------------------------------------------------

; Let Robert and Joe be two processes that want to communicate. 
; - Robert sends greetings to Joe.
; - Joe returns the greeting, then sends a goodbye message. 
; - Robert receives the message, also sends a goodbye message, and terminates. 
; - Joe receives the goodbye message and terminates.

#| Robert exectues:
  Joe ! hello_joe,
  receive
    {Joe, hello_robert} ->
      receive {Joe, goodbye_robert} ->
        Joe ! goodbye_joe
        robert_ok
      end
  end.

  Where Robert's Pid is 0 and Joe's Pid is 1.
|#
(defconst *robert*
  (make-exprs-proc
    '(:pid 0) '((Joe :pid 1))
    '((:binop ! (:var Joe) (:tuple (:cons (:call self (:nil)) (:cons (:atom hello_joe) (:nil)))))
      (:receive
        (((cases (:tuple (:cons (:var Joe) (:cons (:atom hello_robert) (:nil)))))
          (guards)
          (body
            (:receive
              (((cases (:tuple (:cons (:var Joe) (:cons (:atom goodbye_robert) (:nil)))))
                (guards)
                (body 
                  (:binop !
                    (:var Joe)
                    (:tuple (:cons (:call self (:nil)) (:cons (:atom goodbye_joe) (:nil)))))
                  (:atom robert_ok))))))))))))

#| Joe exectues:
  receive
    {Robert, hello_joe} ->
      Robert ! hello_robert,
      Robert ! goodbye_robert,
      receive {Robert, goodbye_joe} ->
        joe_ok
      end
  end.

  Where Robert's Pid is 0 and Joe's Pid is 1.
|#
(defconst *joe*
  (make-exprs-proc
    '(:pid 1) '((Robert :pid 0))
    '((:receive
       (((cases (:tuple (:cons (:var Robert) (:cons (:atom hello_joe) (:nil)))))
         (guards)
         (body
          (:binop !
            (:var Robert)
            (:tuple (:cons (:call self (:nil)) (:cons (:atom hello_robert) (:nil)))))
          (:binop !
            (:var Robert)
            (:tuple (:cons (:call self (:nil)) (:cons (:atom goodbye_robert) (:nil)))))
          (:receive
            (((cases (:tuple (:cons (:var Robert) (:cons (:atom goodbye_joe) (:nil)))))
              (guards)
              (body (:atom joe_ok))))))))))))


; A network of Erlang processes concisting of Joe and Robert.
(defconst *network* (omap::from-lists '((:pid 0) (:pid 1)) (list *robert* *joe*)))

; Run the processes with: (erl-runner *network* 20)

(assert-equal
  (erl-state->in (proc->s (omap::lookup '(:pid 0) (erl-runner *network* 20))))
  '(:atom robert_ok))

(assert-equal
  (erl-state->in (proc->s (omap::lookup '(:pid 1) (erl-runner *network* 20))))
  '(:atom joe_ok))