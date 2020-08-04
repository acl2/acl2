Shellpool Documentation
=======================

See also the [Installation](INSTALL.md) instructions.


## Minimal Example

The typical way to use Shellpool is to `start` some bash processes and
then `run` some commands.

```
$ ccl                                ;; start lisp
? (ql:quickload :shellpool)          ;; load shellpool (see installation instructions!)
? (shellpool:start)                  ;; start a bash shell
? (shellpool:run "echo hello")       ;; run a command
hello                                ;; some output printed by the command
0                                    ;; the resulting exit status
```

Why are `start` and `run` separated?  Launching external programs involves
[forking](http://en.wikipedia.org/wiki/Fork_%28operating_system%29) your Lisp.
Forking is **not reliable** when your Lisp has many GB of memory allocated or
multiple threads are already running.  (Here are
[some](http://www.linuxprogrammingblog.com/threads-and-fork-think-twice-before-using-them)
[articles](http://bryanmarty.com/2012/01/14/forking-jvm/) for background.)

Separating `start` from `run` largely solves these problems: you can `start`
your shells early while your program is booting up, before creating any helper
threads or allocating lots of memory.  You can then freely `run` external
programs from these shells without having to fork Lisp.


## Starting Shells

### `(start [n]) --> nil`

Examples:
```
(shellpool:start)       ;; start a single bash shell
(shellpool:start 3)     ;; start 3 more bash shells
(shellpool:start 10000) ;; causes an error
```

The `start` command launches bash shells that can be used for running
sub-commands.  Typically `start` is only called once at the start of your
program, but you can also call it subsequently to start up additional shells,
as shown above.

How many shells should you start?  The number of shells you create will limit
how many simultaneous external programs you can `run` at a time.  So:

 - If your Lisp program is single-threaded, a single shell will be fine.

 - If your Lisp program is multi-threaded (e.g., a web server or similar), and
   you need to be able to invoke external programs from many threads, then you
   may want many shells.  (The `run` command will wait until a shell becomes
   available, so running out of shells might throttle your program.)

As a basic precaution, `start` will call `error` if you try to create more than
`shellpool:*max-shells*`, which defaults to `1000`.


### `(ensure [n]) --> nil`

Examples:

```
(shellpool:ensure)       ;; make sure at least 1 bash shell is running
(shellpool:ensure 3)     ;; make sure at least 3 bash shells are running
(shellpool:ensure 10000) ;; causes an error
```

The `ensure` command makes sure that at least `n` bash shells are available for
running sub-commands.  This is nearly identical to `start`, except that
`ensure` considers how many shells are already running.

Example 1.  Suppose you have 5 shells already running.

  - `(shellpool:start 3)` would leave you with 8 shells running, but
  - `(shellpool:ensure 3)` would leave you with 5 shells running.

Example 2:  Suppose you have 1 shell running.

  - `(shellpool:start 3)` would leave you with 4 shells running, but
  - `(shellpool:ensure 3)` would leave you with 3 shells running.

Note that `ensure` also considers `shellpool:*max-shells*` and will call
`error` if you try to create too many shells.



## Running Commands

### `(run script [options]) --> exit-status`

Examples:
```
(shellpool:run "echo hello")
(shellpool:run "convert-image photo.png" :each-line #'parse-convert-image)
```

The `run` function runs a bash script and waits for it to finish (so it can
give you the exit status).  For instance, you can expect `(time (shellpool:run
"sleep 5"))` to report something like 5.001 seconds and return 0.

The `run` command will call `error` if no shells have been started.  Otherwise,
it will try to reserve a shell and use it to run your script.

The `script` to execute must be a string.  This string will be written into a
temporary script that will be run by `bash`.  You can, therefore, write whole
bash scripts and freely make use of functions, sequences of commands, etc.

The temporary script will be run with `/dev/null` as its input.  This isn't
suitable for running scripts that need to prompt the user for input.


### Handling Output

By default, output that your `script` prints is forwarded sensibly:

  - output to `stdout` goes to `*standard-output*`
  - output to `stderr` goes to `*error-output*`

An easy way to change where the output goes is to `let`-bind these streams.
For instance, to collect `stdout` instead of streaming it, you could do this:

```
? (let* ((stream            (make-string-output-stream))
         (*standard-output* stream))
    (shellpool:run "echo Hello")
    (shellpool:run "echo World")
    (get-output-stream-string stream))
"Hello
World
"
```

For more flexibility, you can write your own line-handling function.  Your
function will get the `line` to process and its `type` (i.e., whether it is a
`stdout` or `stderr` line).  For example:

```
? (defun my-handle-line (line type)
    (format t "On ~s, got ~s~%" type line))

? (shellpool:run "echo hello
                  echo world 1>&2
                  echo foo
                  echo bar 1>&2
                  exit 7"
                 :each-line #'my-handle-line)
On :STDERR, got "world"
On :STDERR, got "bar"
On :STDOUT, got "hello"
On :STDOUT, got "foo"
7                          ;; <-- return value from (shellpool:run ...)
```

You can use this to collect up output, transform it on the fly, filter it,
stream it to any number of places, etc.  For example, here is a way to
separately collect the stdout and stderr lines without any streaming:

```
? (defun fancy-runner (cmd)
    (let ((out-lines nil)
	  (err-lines nil)
	  (return-code nil))
      (setq return-code
	    (shellpool:run cmd
                           :each-line
                           (lambda (line type)
                             (case type
                               (:STDOUT (push line out-lines))
                               (:STDERR (push line err-lines))
                               (otherwise (error "unexpected line type from shellpool: ~s" type))))))
      (list :return-code return-code
            :out-lines (nreverse out-lines)
            :err-lines (nreverse err-lines))))

? (fancy-runner "echo hello
                 echo world 1>&2
                 echo foo
                 echo bar 1>&2")
(:RETURN-CODE 0 :OUT-LINES ("hello" "foo") :ERR-LINES ("world" "bar"))
```


### Aborting Programs

Sometimes you may not want to wait for your script to finish.  For instance:

  - You may be streaming the output from your script into your Lisp's
    read-eval-print loop.  If your script (or some program it calls) is running
    slowly or misbehaving in some way, you may want to interrupt it and get
    back to the Lisp prompt.

  - You may be parsing the output from your script as it is produced using
    custom `each-line` functions.  Your parser might notice that your script is
    having problems or producing invalid output, and you may want to call
    `error` instead of letting the script continue to run.

In these situations, you would like to quickly and cleanly terminate your
script and make the shell it was using become available again.

Shellpool's `run` uses `unwind-protect` to clean up in case of errors or
interrupts.  In short, this involves:

  - killing your script and any processes it has started (with `kill -9`)

  - flushing any remaining output from your script (and ignoring it, i.e., any
    extra output is not streamed anywhere or sent to `each-line`)

  - deleting the temporary shell script file

This behavior should work well in most cases.  However, it will **not** work
well if your sub-programs are unsafe to kill, e.g., because killing them will
cause you to lose valuable data.

There are other various caveats...

  - To kill your program and the programs it has spawned, we walk the process
    listing to figure out all of the children processes, recursively, and then
    send kill signals to them.  If your program (or its descendents) are
    rapidly creating new processes, then we may not kill them all because time
    will pass between our process listing and kill commands.

  - On Windows, the killing mechanism should work well for Cygwin processes,
    but it may not work well with native Windows programs.


## Background Commands

### `(run& script) --> nil`

Examples:
```
(shellpool:run& "xclock")
(shellpool:run& "firefox http://localhost:9876/")
```

The `run&` command can be used to run a scripts in the background.  Unlike
`run`, which waits for your script to finish so that you can capture its output
and exit code, `run&` simply starts your script and then returns without
waiting.

This may be useful for launching separate programs for the user to interact
with, or for starting long-running jobs that don't need to be monitored.


## Stopping Shells

Shellpool does not currently provide a way to stop the shells after they have
been created.

