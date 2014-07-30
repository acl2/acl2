#!/usr/bin/env ruby

# ACL2 Bridge -- Basic Ruby Interface
# Copyright (C) 2012 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# License: (An MIT/X11-style license)
#
#   Permission is hereby granted, free of charge, to any person obtaining a
#   copy of this software and associated documentation files (the "Software"),
#   to deal in the Software without restriction, including without limitation
#   the rights to use, copy, modify, merge, publish, distribute, sublicense,
#   and/or sell copies of the Software, and to permit persons to whom the
#   Software is furnished to do so, subject to the following conditions:
#
#   The above copyright notice and this permission notice shall be included in
#   all copies or substantial portions of the Software.
#
#   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
#   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
#   DEALINGS IN THE SOFTWARE.
#
# Original author: Jared Davis <jared@centtech.com>

require 'getopt/long'
require_relative 'ACL2Bridge.rb'

debug = false

PROGRAM_NAME = $0

HELP_MESSAGE = <<END
Demo Client for ACL2 Bridge in Ruby

USAGE:  #{PROGRAM_NAME} [OPTIONS] --socket FILE
            or
        #{PROGRAM_NAME} [OPTIONS] --host HOST[:PORT]

The --socket form connects to a local acl2-bridge server over a unix domain
socket.  FILE is the name of the socket file where the server is listening.

The --host form connects to a remote acl2-bridge server at HOST.  The :PORT
can be omitted and defaults to #{ACL2Bridge::DEFAULT_PORT}.

OPTIONS:

   -h                    Show this help message and exit.
   --help

   -d                    Print verbose debugging messages.
   --debug

END

opts = Getopt::Long.getopts(["--socket", "", Getopt::REQUIRED],
                            ["--host", "", Getopt::REQUIRED],
                            ["--help", "-h"],
                            ["--debug", "-d"])

if opts["debug"]
  debug = true
end

if opts["help"]
  puts HELP_MESSAGE
  exit(0)
end

if opts["socket"] and opts["host"]
  puts "Error: can't connect to both a --socket and a --host."
  puts "See --help for usage"
  exit(1)
end

if !opts["socket"] and !opts["host"]
  puts "Error: need at least --socket or --host."
  puts "See --help for usage"
  exit(1)
end

host = opts["host"]
port = ACL2Bridge::DEFAULT_PORT
if (opts["host"] =~ /^(.*):([0-9]+)$/)
  host = $1
  port = $2
end

def read_command()
  print "\ndemo > "
  input = ""
  STDIN.each_line { |line|
    input = input + line
    return input if (line == "\n")
  }
  return nil
end

def read_eval_print_loop(bridge, debug)
  while true
    input = read_command
    return unless input
    # Note: this uses the low-level interface, which lets it print the messages
    # it receives in interleaved form.  For web applications, you might prefer
    # higher-level interfaces.
    bridge.send_command(:lisp_mv, input)
    bridge.until_ready { |type, content|
      print "[#{type}]: " if debug
      print content
    }
  end
end

bridge = ACL2Bridge.new(:debug => debug,
                        :socket => opts["socket"],
                        :host => host,
                        :port => port)
puts <<END

Notes: This is a basic read-eval-print loop.

  - Hit ENTER twice to submit a command.

  - Exactly one command at a time is required.
      It is an error to give a partial command, e.g., (+ 1
      It is an error to give multiple commands, e.g., (+ 1 2) (+ 3 4)

  - We use :LISP_MV mode, so (+ 1 2) = (3) instead of 3.  (You're seeing the
    multiple-value-list of the answer.  The bridge has other modes, e.g., for
    single-value output, JSON encoding, etc.)

  - Use EOF to exit and leave the server running, or (quit) to shut down
    the server (and kill your client with an error).

  - Try commands like these, and see how the output gets spilt into multiple
    messages and is separated from the return value:

     (progn (format t "Hello, five is ~a~%" 5)
            (cw "Hello, five is ~x0~%" 5))

    It's too bad how ACL2's printing routines do everything character by
    character.

END

read_eval_print_loop(bridge, debug)
bridge.close


