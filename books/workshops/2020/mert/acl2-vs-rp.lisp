; ADDER RULEs - lemmas to prove ppx adders correct

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "projects/rp-rewriter/top" :dir :system)

(include-book "centaur/svl/top" :dir :system)


(def-rp-rule logand-to-4vec-bitand
  (implies (and (integerp x)
                (integerp y))
           (equal (logand x y)
                  (svl::4vec-bitand x y)))
  :hints (("Goal"
           :expand (svl::4vec-bitand x y)
           :in-theory (e/d (svl::4vec-bitand
                            SV::3VEC-BITAND
                            SV::4VEC->UPPER
                            SV::4VEC->LOWER)
                           (logand)))))

(defthm logand-to-4vec-bitand-side-cond
  (implies (and (integerp x)
                (integerp y))
           (integerp (svl::4vec-bitand x y))))

(rp-attach-sc logand-to-4vec-bitand
              logand-to-4vec-bitand-side-cond)

(define i-assoc (name alist)
  :returns (res integerp)
  (b* ((entry (hons-assoc-equal name alist)))
    (ifix (cdr entry)))
  ///
  (rp::add-rp-rule integerp-of-i-assoc))

(define  bin-fnc-tree (fnc-name
                       (size natp)
                       (cnt natp))
  :verify-guards nil
  :returns (mv term (cnt-res natp :hyp (natp cnt)))
  (if (zp size)
      (mv `(,fnc-name (i-assoc ',(sa 'var cnt) env)
                      (i-assoc ',(sa 'var (1+ cnt)) env))
          (+ cnt 2))
    (b* (((mv term1 cnt)
          (bin-fnc-tree fnc-name (1- size) cnt))
         ((mv term2 cnt)
          (bin-fnc-tree fnc-name (1- size) cnt)))
      (mv `(,fnc-name ,term1 ,term2)
          cnt)))
  ///
  (verify-guards bin-fnc-tree))



(defmacro start-timer ()
  `(make-event
    (b* (((mv time state)
          (read-run-time state)))
      (mv nil
          `(table rp-experiment 'start ,time)
          state))))

(defun get-time-aux (diff n)
  (if (zp n)
      (str::int-to-dec-string (floor diff 1))
    (str::cat (get-time-aux (floor diff 10) (1- n))
              (if (equal n 1) "." "")
              (str::int-to-dec-string (mod (floor diff 1) 10)))))

(defun get-time (diff host-lisp)
  (if (equal host-lisp 'ccl)
      (get-time-aux (* 1000000 diff) 6)
    (get-time-aux (* 1000 diff) 3)))

(defmacro set-host (host)
  `(table host 'host ',host))
(set-host ccl)

(defmacro register-event (event)
  `(make-event
    `(table exp-events 'events
            ',(cons ',event
                    (cdr (assoc-equal 'events (table-alist 'mult-events (w state))))))))

(defmacro end-timer (rewriter size)
  `(make-event
    (b* (((mv end-time state)
          (read-run-time state))
         (start-time (rfix (cdr (assoc-equal 'start
                                             (table-alist 'rp-experiment (w state))))))
         (host (cdr (assoc-equal 'host (table-alist 'host (w state)))))
         (message (str::cat "Proofs with "
                            ,(symbol-name rewriter)
                            " with depth "
                            ,(str::int-to-dec-string size)
                            " finished in "
                            (get-time (- end-time start-time) host)
                            " secs."))
         (- (cw (str::cat "~%" message "~%"))))
      (mv nil
          `(progn
             (register-event ,message)

             (value-triple ,message))
          state))))

(define acl2-rw-event ((size natp))
  ` (with-output
      :off :all
      :gag-mode nil
      (make-event
       (b* (((mv term1 &) (bin-fnc-tree 'logand ,size 0))
            ((mv term2 &) (bin-fnc-tree 'svl::4vec-bitand ,size 0)))
         `(encapsulate
            nil
            (local
             (in-theory (theory 'minimal-theory)))
            (local
             (in-theory (enable logand-to-4vec-bitand
                                logand-to-4vec-bitand-side-cond
                                integerp-of-i-assoc)))

            (start-timer)

            (with-output
              :off :all
              :gag-mode nil
              (thm
               (equal ,term1
                      ,term2)))

            (end-timer acl2 ,,size))))))

(define rp-rw-event ((size natp))
  ` (with-output
      :off :all
      :gag-mode nil
      (make-event
       (b* (((mv term1 &) (bin-fnc-tree 'logand ,size 0))
            ((mv term2 &) (bin-fnc-tree 'svl::4vec-bitand ,size 0)))
         `(encapsulate
            nil
            (local
             (rp::disable-all-rules))
            (local
             (rp::enable-rules '(logand-to-4vec-bitand
                                 ;;logand-to-4vec-bitand-side-cond
                                 integerp-of-i-assoc)))
            (start-timer)
            (with-output
              :off :all
              :gag-mode nil
              (rp-thm
               (equal ,term1
                      ,term2)
               :time nil))
            (end-timer rp-rewriter ,,size))))))

(defconst *maxdepth* 15)

(defun create-events (max-depth)
  (if (zp max-depth)
      (list (rp-rw-event *maxdepth*)
            (acl2-rw-event *maxdepth*))
    (list* (rp-rw-event (1+ (- *maxdepth* max-depth)))
           (acl2-rw-event (1+ (- *maxdepth* max-depth)))
           (create-events (1- max-depth)))))

(comp t) ; added for GCL and perhaps useful for other Lisps besides CCL and SBCL

(make-event
 `(with-output
    :off :all
    :gag-mode nil
    (progn
      .
      ,(create-events *maxdepth*))))
