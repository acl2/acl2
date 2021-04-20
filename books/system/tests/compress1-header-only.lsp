; Copyright (C) 2021, ForrestHunt, Inc.
; Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Load this file in raw Lisp (i.e., start ACL2 and run :q).  Results on
; a 2019-vintage Intel Mac are at the end, below.

; Optional (see table at the end, below):
(set-gc-strategy :delay) ; avoid GC
(defvar *swap* nil) ; do test1 before test0

;;; Start tests.

(defconstant *sz* 250)
(defconstant *sz-1* (1- *sz*))

(defvar *a* (make-array *sz*))

(defvar *names*
  (loop for i fixnum from 0 to *sz-1* collect
        (packn (list 'ar i))))

(defun test0 ()
  (time (loop for i fixnum from 0 to *sz-1*
              do
              (setf (svref *a* i)
                    (make-array 500000 :initial-element 124)))))

(defun test1 ()
  (time (loop for i fixnum from 0 to *sz-1*
              as name in *names*
              do
              (setf (svref *a* i)
                    (compress1 name
                               '((:header :dimensions (500000)
                                          :maximum-length 1000000
                                          :default 124)))))))

(cond ((boundp '*swap*)
       (test1) ; "test1/1": make ACL2 arrays
       (test1) ; "test1/2": recompress ACL2 arrays
       (test0) ; make arrays
       )
      (t
       (test0) ; make arrays
       (test1) ; "test1/1": make ACL2 arrays
       (test1) ; "test1/2": recompress ACL2 arrays
       ))

;;; Here are results in seconds (GC in {..}, if any).
;;; "Patch?" is "Y" when running after the change around April 9, 2021, to
;;; speed up compress1 (see :doc note-8-4); it's "N" before that change.
#||

patch?	no GC?	swap?	test0{GC}		test1/1			test1/2
--------------------------------------------------------------------------------
  N       N       N	1.618475{1.289835}	2.461975{1.991867}	0.487191
  Y       N       N	1.632488{1.308580}	2.284671{2.044107}	0.234406

  N       Y       N	0.335618		0.552878		0.484963
  Y       Y       N	0.339081		0.343174		0.232085

  N       N       Y	2.672724{2.349363}	1.849991{1.286574}	0.485177
  Y       N       Y	2.668920{2.342377}	1.618786{1.291710}	0.232350

  N       Y       Y	0.316486		0.566139		0.486522
  Y       Y       Y	0.316941		0.365097		0.242303

||#
