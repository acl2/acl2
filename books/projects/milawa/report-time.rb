#!/usr/bin/env ruby

# Milawa Time Report Tool - Jared Davis (jared@cs.utexas.edu)
#
# You just feed this the output from Milawa, and it tells you which events tool
# the longest.  Note that GC performance can randomly make some events look bad
# even when it's "not their fault."
#
# Example Usage:
#
#   ./report-time.rb < utilities.ccl-image.out
#
# Example Output
#
#     43.62   VERIFY FORCING-TRICHOTOMY-OF-<< (#1616)
#     34.27   VERIFY ORDERED-SUBSETP-IS-TRANSITIVE (#1499)
#     31.26   VERIFY LEMMA2-FOR-GATHER-CONSTANTS-FROM-EQUAL-OF-PLUS-AND-PLUS (#265)
#     28.01   VERIFY EQUAL-OF-APP-AND-APP-WHEN-EQUAL-LENS (#446)
#     27.75   VERIFY CONS-LISTP-OF-REMOVE-SUPERSETS1 (#1000)
#     ... and so on ...

data = Array.new

while line = STDIN.gets
   case line
     when /([0-9]+)> (VERIFY|DEFINE) (.*)/
        current = { :event => $1, :type => $2, :name => $3 }
     when /;; (VERIFY|DEFINE) took ([0-9]+\.[0-9]+) seconds/
        current[:time] = $2.to_f
        data.push(current)
   end
end

sorted = data.sort_by { |x| -x[:time] }
sorted.each { |x|
  printf("%10.2f   %s %s (#%s)\n", x[:time], x[:type], x[:name], x[:event])
}
