# Usage racc datatypes.y.rb && ruby datatypes.tab.rb
#
# Simple ML like language using Scott encoding

class Parser
  prechigh
    left '->'
  preclow

  token WORD INT BOOL STRING
  options no_result_var


  start main

  rule

  main : stmts { [val[0]].flatten }

  stmts : stmts ";" stmt { [val[0], val[2]] } | stmt
  stmt : val | expr_0

  val : "val" WORD "=" expr_0 { Val.new(val[1], val[3]) }

  expr_0 : typ_intro | typ_scheme | lamb | let | if_ | expr_1
  expr_1 : bin_expr | expr_2
  expr_2 : app | expr_3
  expr_3 : atom

  bin_expr : expr_1 bin_op expr_2 { TypApp.new("(#{val[1]})".to_sym, TypApp.new(val[0], val[2])) }
  bin_op : "->" | "+" | "*" | "-" | "/" | "." | "|"
  typ_intro : "type" WORD ":" expr_0 "=>" expr_0 { TypIntro.new(val[1], val[3], val[5]) }
  lamb : "func" WORD ":" expr_0 "=>" expr_0 { Lamb.new(val[1], val[3], val[5]) }
  app : expr_2 expr_3 { App.new(val[0], val[1]) }
  atom : WORD 
       | const 
       | "(" expr_0 ")" { val[1] } 
  const : INT | BOOL | STRING
  let : "let" WORD "=" expr_0 "in" expr_0
      { Let.new(val[1], val[3], val[5]) }
  if_ : "if" expr_0 "then" expr_0 "else" expr_0
      { If.new(val[1], val[3], val[5]) }

  typ_scheme : "forall" WORD "." expr_0 { TypScheme.new(val[1], val[3]) }
end

---- inner
KEYWORDS = %w(type data match with end let in func val if then else true false forall)
SYMBOLS = %w(=> -> . | ; = ( ) : + - * /).map { |x| Regexp.quote(x) }

def readstring(s)
  acc = []
  loop do
    x = s.scan_until(/"|\"/)
    fail "unterminated string \"#{str}" if x.nil?
    if x.end_with? '\"'
      acc << x
    else
      acc << x[..-2]
      break
    end
  end
  acc.join("")
end

def make_tokens str
  require 'strscan'

  result = []
  s = StringScanner.new str
  until s.empty?
    case
    when s.skip(/\s+/)
    when s.scan(/#/)
      s.skip_until(/$/)
    when tok = s.scan(/(#{SYMBOLS.join("|")})/)
      result << [tok, tok.to_sym]
    when tok = s.scan(/\b(#{KEYWORDS.join("|")})\b/)
      case tok
      when "true"
        result << [:BOOL, true]
      when "false"
        result << [:BOOL, false]
      else
        result << [tok, tok.to_sym]
      end
    when tok = s.scan(/"/)
      result << [:STRING, readstring(s)]
    when tok = s.scan(/\d+/)
      result << [:INT, tok.to_i]
    when tok = s.scan(/\w+/)
      result << [:WORD, tok.to_sym]
    else
      raise "can't recognize  <#{s.peek(5)}>"
    end
  end
  result << [false, false]
  return result
end

attr_accessor :result

def parse(str)
  @result = []
  @tokens = make_tokens str
  do_parse
end

def next_token
  @tokens.shift
end

---- header

module Unparsable
  def to_s; Unparser.new.unparse([self]); end
end

class DataType < Struct.new :name, :args, :ctrs; include Unparsable; end
class Ctr < Struct.new :name, :args; include Unparsable; end
class App < Struct.new :f, :arg; include Unparsable; end
class Let < Struct.new :x, :e1, :e2; include Unparsable; end
class Lamb < Struct.new :arg, :typ, :body; include Unparsable; end
class Val < Struct.new :name, :value; include Unparsable; end
class Match < Struct.new :scrutinee, :patterns; include Unparsable; end
class MatchPattern < Struct.new :pat, :body; include Unparsable; end
class If < Struct.new :cond, :then_, :else_; include Unparsable; end
class TypScheme < Struct.new :var, :expr; include Unparsable; end
class TypIntro < Struct.new :var, :kind, :expr; include Unparsable; end
class TypApp < Struct.new :typ, :arg; include Unparsable; end
class TypFun < Struct.new :tin, :tout; include Unparsable; end
