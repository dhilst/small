# Usage racc datatypes.y.rb && ruby datatypes.tab.rb
#
# Simple ML like language using Scott encoding

class Parser
  token WORD INT BOOL STRING
  options no_result_var

  start main

  rule

  main : stmts { [val[0]].flatten }

  stmts : stmts ";" stmt { [val[0], val[2]] } | stmt
  stmt : data | val | expr_0

  data : "data" WORD args "=" ctrs
       { DataType.new(val[1], [val[2]].flatten, [val[4]].flatten) }
       | "data" WORD "=" ctrs
       { DataType.new(val[1], nil, [val[3]].flatten)  }
  args : args WORD { [val[0], val[1]] } | WORD
  ctrs : ctr "|" ctrs { [val[0], val[2]] }
       | ctr
  ctr : ctr WORD { Ctr.new(val[0].name, [*val[0].args, val[1]].flatten) }
      | WORD { Ctr.new(val[0]) }

  val : "val" WORD "=" expr_0 { Val.new(val[1], val[3]) }

  expr_0 : lamb | let | if_ | match | expr_1
  expr_1 : app | expr_2
  expr_2 : atom

  lamb : "fun" WORD "=>" expr_0 { Lamb.new(val[1], nil, val[3]) }
  app : expr_1 expr_2 { App.new(val[0], val[1]) }
  atom : WORD | const | "(" expr_0 ")" { val[1] }
  const : INT | BOOL | STRING
  let : "let" WORD "=" expr_0 "in" expr_0
      { Let.new(val[1], val[3], val[5]) }
  match : "match" expr_0 "with" patterns "end"
  { Match.new(val[1], [val[3]].flatten) }
  if_ : "if" expr_0 "then" expr_0 "else" expr_0
      { If.new(val[1], val[3], val[5]) }
  patterns : pattern patterns { [val[0], val[1]] }
           | pattern
  pattern : "|" pat "=>" expr_0 { MatchPattern.new(val[1], val[3]) }
  pat : WORD pat { [val[0], val[1]].flatten } | WORD
end

---- inner
KEYWORDS = %w(data match with end let in fun val if then else true false)
SYMBOLS = %w(=> | ; = ( ) :).map { |x| Regexp.quote(x) }


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
      result << [tok, nil]
    when tok = s.scan(/\b(#{KEYWORDS.join("|")})\b/)
      case tok
      when "true"
        result << [:BOOL, true]
      when "false"
        result << [:BOOL, false]
      else
        result << [tok, nil]
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

class DataType < Struct.new :name, :args, :ctrs; def to_s; Unparser.new.unparse([self]); end; end
class Ctr < Struct.new :name, :args; def to_s; Unparser.new.unparse([self]); end; end
class App < Struct.new :f, :arg; def to_s; Unparser.new.unparse([self]); end; end
class Let < Struct.new :x, :e1, :e2; def to_s; Unparser.new.unparse([self]); end; end
class Lamb < Struct.new :arg, :typ, :body; def to_s; Unparser.new.unparse([self]); end; end
class Val < Struct.new :name, :value; def to_s; Unparser.new.unparse([self]); end; end
class Match < Struct.new :scrutinee, :patterns; def to_s; Unparser.new.unparse([self]); end; end
class MatchPattern < Struct.new :pat, :body; def to_s; Unparser.new.unparse([self]); end; end
class If < Struct.new :cond, :then_, :else_; def to_s; Unparser.new.unparse([self]); end; end
