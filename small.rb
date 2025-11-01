require "pry"
require "set"
require "readline"
require "fileutils"
require "./parser"

puts(Parser.new.parse($stdin.read))

