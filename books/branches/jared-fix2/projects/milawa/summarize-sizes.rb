#!/usr/bin/env ruby -w

def fix_string(str)
  # strip color codes by turning escape char into ?.
  len = str.length
  for n in 0..len
    str[n] = '?' if (str.getbyte(n) == 27)
  end
  return str
end

def pretty_number(n)
  # insert commas appropriately
  return n.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse
end


def get_cons_sizes(dir)
  # read proof sizes from pcert.out files in bootstrap dirs
  sizes = Array.new
  Dir["ACL2/bootstrap/#{dir}/*.pcert.out"].each { |path|
    File.open(path).each { |line|
      line = fix_string(line)
      case line
      when /;; Proof sizes total: ([0-9,]+) conses.*/
        size = $1.gsub(/\,/,"") # eats commas
        sizes.push(size.to_i)
      when /;; Proof size: ?.*m([0-9,]+) conses.*/
        size = $1.gsub(/\,/,"") # eats commas
        sizes.push(size.to_i)
      end
    }
  }
  return sizes
end

def get_file_sizes(dir)
  # read actual file sizes from proof files in Proofs dirs
  sizes = Array.new
  Dir["Proofs/#{dir}/*.*"].each { |path|
    sizes.push(File.size(path))
  }
  return sizes
end

def human_file_size(size)
  # These terms are, of course, ambiguous.  We use powers of 10.
  kilobyte = 1000
  megabyte = 1000*kilobyte
  gigabyte = 1000*megabyte
  return "#{size} B" if (size < kilobyte)
  return "#{("%0.1f" % (size.to_f/kilobyte))} KB" if (size < megabyte)
  return "#{("%0.1f" % (size.to_f/megabyte))} MB" if (size < gigabyte)
  return "#{("%0.1f" % (size.to_f/gigabyte))} GB"
end

def human_cons_size(size)
  kilocons = 1000
  megacons = 1000*kilocons
  gigacons = 1000*megacons
  return "#{size} C" if (size < kilocons)
  return "#{("%0.1f" % (size.to_f/kilocons))} KC" if (size < megacons)
  return "#{("%0.1f" % (size.to_f/megacons))} MC" if (size < gigacons)
  return "#{("%0.1f" % (size.to_f/gigacons))} GC"
end

def summarize_events(dir)
  define = 0
  verify = 0
  skolem = 0
  switch = 0
  finish = 0

  File.open("Proofs/#{dir}.events").each { |line|
    case line
    when /\(DEFINE.*/
      define += 1
    when /\(VERIFY.*/
      verify += 1
    when /\(SKOLEM.*/
      skolem += 1
    when /\(SWITCH.*/
      switch += 1
    when /\(FINISH.*/
      finish += 1
    end
  }

  total = define + verify + skolem + switch + finish
  return {:define => define, :verify => verify, :skolem => skolem,
  	  :switch => switch, :finish => finish, :total => total }
end

def summarize(dir)

  puts "Processing #{dir}"
  conses = get_cons_sizes(dir)
  max_conses = conses.max
  sum_conses = 0
  conses.each { |x| sum_conses += x }

  big_conses = Array.new
  conses.each { |x| big_conses.push(x) if x > 500000000 }

  files = get_file_sizes(dir)
  max_file = files.max
  sum_files = 0
  files.each { |x| sum_files += x }

  events = summarize_events(dir)

  puts "  Found #{conses.size} proof-size lines in ACL2/bootstrap/#{dir}/*.pcert.out"
  puts "  Found #{files.size} proof files in Proofs/#{dir}"
  puts "  Maximum proof size is: #{pretty_number(max_conses)}"
  puts "  Sum of proof sizes is: #{pretty_number(sum_conses)}"
  puts "  Number of big (over 500 megaconses) proofs is: #{big_conses.size}"
  puts "  Sizes of big proofs (in conses) are: #{big_conses}"
  puts "  Total size of proof files on disk is: #{human_file_size(sum_files)}"
  puts "  Largest individual proof file is: #{human_file_size(max_file)}"
  puts "  Event counts: #{events}"
  puts ""

  return {:dir => dir,
          :definitions => events[:define],
          :theorems => events[:verify],
          :max_conses => max_conses,
          :sum_conses => sum_conses,
          :total_file_size => sum_files}


end


def latex_fix_dirname(dir)
  return "leveltwo" if dir == "level2"
  return "levelthree" if dir == "level3"
  return "levelfour" if dir == "level4"
  return "levelfive" if dir == "level5"
  return "levelsix" if dir == "level6"
  return "levelseven" if dir == "level7"
  return "leveleight" if dir == "level8"
  return "levelnine" if dir == "level9"
  return "levelten" if dir == "level10"
  return "leveleleven" if dir == "level11"
  return dir
end


dirs = ["utilities", "logic", "level2", "level3", "level4", "level5", "level6",
        "level7", "level8", "level9", "level10", "level11", "user"]

results = Array.new
dirs.each { |x| results.push(summarize(x)) }


puts ""
puts "%% Table for LaTeX:"
puts ""

puts "\\begin{tabular}{lrrrrr}"
puts "\\textbf{Directory} & \\textbf{Defs} & \\textbf{Thms} &"
puts "\\textbf{Largest Proof} & \\textbf{All Proofs} & \\textbf{Disk Size} \\\\"
puts " & & & (megaconses) & (megaconses) & (megabytes) \\\\"
puts "\\hline"


def pretty_float(float)
  ipart = float.to_i
  fpart = (float * 10).to_i % 10
  return "#{pretty_number(ipart)}.#{fpart}"
end






totdefs = 0
totthms = 0
totsums = 0
totfile = 0

macros = File.open("size_macros.tex", "w")

results.each { |x|

  totdefs += x[:definitions]
  totthms += x[:theorems]
  totsums += x[:sum_conses]
  totfile += x[:total_file_size]

  dir = x[:dir].capitalize
  defs = pretty_number(x[:definitions])
  thms = pretty_number(x[:theorems])
  mcons = pretty_float(x[:max_conses].to_f/(1000*1000))
  scons = pretty_float(x[:sum_conses].to_f/(1000*1000))
  tot =   pretty_float(x[:total_file_size].to_f/(1000*1000))
  puts "#{dir} \\quad & #{defs} & #{thms} & #{mcons} & #{scons} & #{tot} \\\\"

  ltxdir = latex_fix_dirname(x[:dir])
  macros.puts("\\newcommand{\\#{ltxdir}numdefs}{#{defs}\\xspace}")
  macros.puts("\\newcommand{\\#{ltxdir}numthms}{#{thms}\\xspace}")
  macros.puts("\\newcommand{\\#{ltxdir}maxconses}{#{human_cons_size(x[:max_conses])}\\xspace}")
  macros.puts("\\newcommand{\\#{ltxdir}sumconses}{#{human_cons_size(x[:sum_conses])}\\xspace}")
  macros.puts("\\newcommand{\\#{ltxdir}filesize}{#{human_file_size(x[:total_file_size])}\\xspace}")
}

macros.close

puts "\\hline"

puts "\\textbf{Totals} & #{pretty_number(totdefs)} & #{pretty_number(totthms)} "
puts "  &              & #{pretty_float(totsums/(1000*1000))} & #{pretty_float(totfile/(1000*1000))} \\\\"
puts "\\end{tabular}"
