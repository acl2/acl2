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

require 'socket'
require 'hash_keyword_args'

class ACL2Bridge

  DEFAULT_PORT = 55433

  def initialize(args={})
    args = args.keyword_args(:name => "ACL2",
                             :debug => false,
                             :port => DEFAULT_PORT,
                             :host => nil,
                             :socket => nil)
    @name = args[:name]
    @debug = args[:debug]

    if args[:socket]
      debug "connecting to socket #{args[:socket]}." if @debug
      @sock = UNIXSocket.new(args[:socket])
    else
      debug "connecting to server #{args[:host]} on port #{args[:port]}." if @debug
      @sock = TCPSocket.new(args[:host], args[:port])
    end

    # The below assignment to worker is subtle.  The hello message
    # that the server sends to the client is something like the
    # following, where bridge-worker-17 is the name of the CCL thread
    # that is running to handle this client.  This name is sent as the
    # content of the hello message and saved so that the Ruby side can
    # know the name of the worker being used.  This name is currently
    # unused but might later but used to implement interrupts.

    # HELLO [n]
    # bridge-worker-17
    type, content = read_message()
    if type == :acl2_bridge_hello
      @worker = content
    else
      raise "Expected hello message, but got: #{type}: #{content}"
    end

    type, content = read_message()
    if type != :ready
      raise "Expected ready message, but got: #{type}: #{content}"
    end
  end


  def close()
    # Note that, obviously, outstanding reads/writes will fail after you close
    # the connection.
    @sock.close()
  end


  def send_command(type, cmd)
    # LOW LEVEL.  You probably want something higher level.  See below.
    #
    # This sends a single command to the server.  It doesn't wait for a
    # reply. The TYPE should be one of the accepted command types, e.g., :json,
    # :lisp, :json_mv, etc.  The CMD should be a single, whole Lisp command.
    @sock.write(type.to_s.upcase)
    @sock.write(" ")
    @sock.write(cmd.length)
    @sock.write("\n")
    @sock.write(cmd)
    @sock.write("\n")
    @sock.flush
  end


  def read_message()
    # LOW LEVEL.  You probably want something higher level.  See below.
    #
    # This reads a single message from the server, and returns the message type
    # (as a lowercase Ruby symbol) and content.  This won't return until the
    # server prints a message to you!
    debug "read_message waiting for header." if @debug
    header = @sock.gets

    case header
    when /^([A-Za-z][A-Za-z0-9_]*) ([0-9]+)$/
      type = $1
      len = Integer($2)
    else
      raise "Invalid header: #{header}"
    end

    debug "read_message got header #{header.strip}, waiting for content." if @debug
    content = @sock.read(len)
    if content.length != len
      raise "Bad #{type} message: expected #{len} bytes, got #{content.length} bytes"
    end

    debug "read_message got content, waiting for newline." if @debug
    newline = @sock.read(1)
    if newline != "\n"
      raise "Bad #{type} message: expected a newline after #{len} bytes, but found #{newline}"
    end

    debug "read_message all done." if @debug

    return type.downcase.intern, content

  end


  def until_ready
    # LOW LEVEL.  You probably want something higher level.  See below.
    #
    # This lets you read messages until the :READY message.  This is a simple
    # way to get the server's response.  Typical usage is:
    #
    #    bridge.until_ready {|type, content|
    #      dostuff(type, content)
    #    }
    #
    # You probably shouldn't use this unless you really need to be able to
    # process the output messages in an incremental fashion.
    #
    # You might need to do this if output is being sent to different channels
    # (e.g., stdout versus stderr) and you don't want it to be separated, but
    # in that case it'd probably be best to write an alternative to
    # raw_command_with_errors that merges messages to those channels.
    #
    # You might also need this if you are just dealing with so much output that
    # it isn't tolerable to wait for the full reply to be collected up by
    # raw_command_with_errors.
    type = nil
    while type != :ready
      type, content = read_message()
      yield type, content
    end
  end


  def raw_command_with_errors (type, cmd, stream=nil)
    # MID LEVEL.  You probably want something higher level.  See below.
    #
    # TYPE and CMD are as in send_command.  We run the command, then read all
    # of the messages of the reply, and return a single hash that associates
    # message-types to their appended together content.
    #
    # STREAM defaults to NIL.  When you give a stream, it must support << and
    # FLUSH.  Any messages of type :stdout are immediately printed to the
    # stream with <<, and then the stream is flushed.  This is useful for
    # relaying status messages from long-running commands.
    #
    # Typical usage:
    #   reply = bridge.raw_command_with_errors("(+ 1 2)")
    #   puts "Output was #{reply[:stdout]}"
    #   puts "Return value was #{reply[:return]}"
    #
    # This is only a "medium level" command because it does not do any kind of
    # error checking on the reply and doesn't try to interpret the return value
    # in any way.  You can't assume that the reply will have a :return or a
    # :stdout or anything.  For instance, if there's a parse error reading the
    # command, then you won't have a :return but you'll have an :error.
    send_command(type, cmd)
    reply = {:cmd => cmd}
    until_ready { |type, content|
      reply[type] = "" unless reply[type]
      reply[type] << content
      if stream and (type == :stdout or type == :error)
        stream << content
        stream.flush
      end
    }
    return reply
  end


  def raw_command(type, cmd, stream=nil)
    # MID LEVEL.  You probably want something higher level.  See below.
    #
    # TYPE, CMD, and STREAM are as above.  We run the command, then read all of
    # the messages of the reply, check to make sure that there were no Lisp
    # errors, and returns a single hash that associates message-types to their
    # appended together content.
    #
    # Typical usage:
    #   reply = bridge.raw_command("(+ 1 2)")
    #   puts "Output was #{reply[:stdout]}"
    #   puts "Return value was #{reply[:return]}"
    #
    # We make sure that the reply has a :return and no :error.  If there is a
    # Lisp :error, we raise it as a Ruby error.
    reply = raw_command_with_errors(type, cmd, stream)
    raise "ACL2 reply has an :error: #{reply}" if reply[:error]
    raise "ACL2 reply has no :return: #{reply}" unless reply[:return]
    return reply
  end


  def json_command (cmd, stream=nil)
    # HIGH LEVEL.  Run a command in JSON mode.  Notice and raise any errors.
    # We return a Ruby string which should be a valid JSON-encoded object.  The
    # object might look like this:
    #
    #   { "stdout":"blah blah blah",
    #     "return":["a":5, "b":6] }
    #
    # That is, it is valid JSON text that contains the standard output
    # and return value (and perhaps in the future other contents).
    reply = raw_command(:json, cmd, stream)
    ret = "{";
    reply.each_pair do |k, v|
      next if k == :return # return is already valid json
      ret << k.to_json
      ret << ":"
      ret << v.to_json
      ret << ",\n"
    end
    ret << "\"return\":"
    ret << reply[:return]
    ret << "}"
    return ret
  end


  private
  def debug(str)
    puts "; ACL2Bridge: #{@name}: #{str}"
  end

end



