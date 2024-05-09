(in-package #:local-time.test)

(defsuite* (comparison :in simple))

(defmacro defcmptest (comparator-name &body args)
  `(deftest ,(symbolicate 'test/simple/comparison/ comparator-name) ()
    (flet ((make (day &optional (sec 0) (nsec 0))
             (make-timestamp :day day :sec sec :nsec nsec)))
      ,@(loop
          :for entry :in args
          :when (= (length entry) 1)
            :do (push 'is entry)
          :else
            :do (if (member (car entry) '(t true is) :test #'eq)
                    'is
                    'is)
          collect (let ((body `(,comparator-name (make ,@(second entry))
                                                 (make ,@(third entry)))))
                    (cond
                      ((eq (car entry) 'true)
                       `(is ,body))
                      ((eq (car entry) 'false)
                       `(is (not ,body)))
                      (t (error "Don't know how to interpret ~S" entry))))))))

(defcmptest timestamp<
  (true (1 0 0)
        (2 0 0))
  (true (0 1 0)
        (0 2 0))
  (true (0 0 1)
        (0 0 2))

  (false (2 0 0)
         (1 0 0))
  (false (0 2 0)
         (0 1 0))
  (false (0 0 2)
         (0 0 1)))

(defcmptest timestamp<=
  (true (1 0 0)
        (2 0 0))
  (true (0 1 0)
        (0 2 0))
  (true (0 0 1)
        (0 0 2))
  (true (1 0 0)
        (1 0 0))
  (true (1 1 0)
        (1 1 0))
  (true (1 1 1)
        (1 1 1))

  (false (2 0 0)
         (1 0 0))
  (false (0 2 0)
         (0 1 0))
  (false (0 0 2)
         (0 0 1)))

(defcmptest timestamp>
  (true (2 0 0)
        (1 0 0))
  (true (0 2 0)
        (0 1 0))
  (true (0 0 2)
        (0 0 1))

  (false (1 0 0)
         (2 0 0))
  (false (0 1 0)
         (0 2 0))
  (false (0 0 1)
         (0 0 2)))

(defcmptest timestamp>=
  (true (2 0 0)
        (1 0 0))
  (true (0 2 0)
        (0 1 0))
  (true (0 0 2)
        (0 0 1))
  (true (1 0 0)
        (1 0 0))
  (true (1 1 0)
        (1 1 0))
  (true (1 1 1)
        (1 1 1))

  (false (1 0 0)
         (2 0 0))
  (false (0 1 0)
         (0 2 0))
  (false (0 0 1)
         (0 0 2)))

(defcmptest timestamp=
  (true (1 0 0)
        (1 0 0))
  (true (1 1 0)
        (1 1 0))
  (true (1 1 1)
        (1 1 1))

  (false (1 0 0)
         (2 0 0))
  (false (0 1 0)
         (0 2 0))
  (false (0 0 1)
         (0 0 2)))

(deftest test/simple/comparison/timestamp=/2 ()
  (is (timestamp= (make-timestamp) (make-timestamp)))
  (is (not (timestamp= (make-timestamp) (make-timestamp :nsec 1)))))

(deftest test/simple/comparison/timestamp=/3 ()
  (is (eql (handler-case
               (timestamp= (make-timestamp) nil)
             (type-error ()
               :correct-error))
           :correct-error)))

(deftest test/simple/comparison/timestamp/= ()
  (is (timestamp/= (make-timestamp :nsec 1) (make-timestamp :nsec 2)))
  (is (timestamp/= (make-timestamp :nsec 1) (make-timestamp :nsec 2) (make-timestamp :nsec 3)))
  (is (not (timestamp/= (make-timestamp :nsec 1) (make-timestamp :nsec 2) (make-timestamp :nsec 1))))
  (is (not (timestamp/= (make-timestamp) (make-timestamp)))))
