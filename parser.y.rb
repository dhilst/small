# Usage racc datatypes.y.rb && ruby datatypes.tab.rb
#
# Simple ML like language using Scott encoding

class Parser
  prechigh
    left '\''
    right '->'
    left '*' '/'
    left '+' '-'
  preclow

  token NAME INT BOOL STRING
  options no_result_var


  start main

  rule

  main : stmts { [val[0]].flatten }

  stmts : stmt ";" stmts { [val[0], val[2]] } 
        | stmt ";" { val[0] }
  stmt : val | typ | expr

  val : "val" NAME ":" expr "=" expr { Val.new(val[1], val[3], val[5]) }
  typ : "typ" NAME "=" expr { Typ.new(val[1], val[3]) }

  expr
    : expr_bin
    | "forall" args "." expr "end" { TypScheme.new(val[1], val[3]) }
    | "(" args ")" "=>" expr "end" { Lamb.new([], val[1], val[4]) }
    | "<" args ">" "=>" expr "end" { Lamb.new(val[1], [], val[4]) }
    | "<" args ">" "(" args ")" "=>" expr "end" { Lamb.new(val[1], val[4], val[7]) }

  args
    : NAME ":" expr "," args { [Arg.new(val[0], val[2]), val[4]].flatten }
    | NAME ":" expr { [Arg.new(val[0], val[2])] }

  expr_bin
    : expr "->" expr { BinOp.new(val[0], "->".to_sym, val[2]) }
    | expr "+" expr { BinOp.new(val[0], "+".to_sym, val[2]) }
    | expr "-" expr { BinOp.new(val[0], "-".to_sym, val[2]) }
    | expr "/" expr { BinOp.new(val[0], "/".to_sym, val[2]) }
    | expr "*" expr { BinOp.new(val[0], "*".to_sym, val[2]) }
    | expr_app

  expr_app 
    : expr_app expr_atom { App.new(val[0], val[1]) }
    | expr_atom

  expr_atom
    : "(" expr ")" { Paren.new(val[1]) }
    | NAME
    | const 

  const : INT;

end

---- inner
KEYNAMES = %w(typ fun val forall end)
SYMBOLS = %w(< > => -> . | ; = ( ) : + - * / ? ,).map { |x| Regexp.quote(x) }

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
    when tok = s.scan(/\b(#{KEYNAMES.join("|")})\b/)
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
      result << [:NAME, tok.to_sym]
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

module Unparser

  def to_s
    show_paren = (ENV["SMALL_SHOW_PAREN"] || "0") != "0";

    case self
    when Typ
      "type #{name} : #{typ};\n"
    when Val
      "val #{name}\n" \
        "  : #{typ}\n" \
        "  = #{value};\n"
    when App
      return "(#{f} #{arg})" if show_paren
      "#{f} #{arg}"
    when Arg
      "#{name} : #{typ}"
    when Lamb
      tyargs_ = tyargs.empty? ? "": "<#{tyargs.join(', ')}>"
      args_ = args.empty? ? "" : "(#{args.join(', ')})"
      "#{tyargs_}#{args_} => #{body} end"
    when TypScheme
      args_ = args.join(", ")
      "forall #{args_} . #{body}"
    when BinOp
      return "(#{fst} #{op} #{snd})" if show_paren
      "#{fst} #{op} #{snd}"
    when Hole
      "?"
    when Paren
      "(#{value})"
    else
      raise "invalid ast node #{self.class}"
    end
  end
end

class Typ < Struct.new :name, :typ; include Unparser; end
class Val < Struct.new :name, :typ, :value; include Unparser; end
class App < Struct.new :f, :arg; include Unparser; end
class Arg < Struct.new :name, :typ; include Unparser; end;
class TypScheme < Struct.new :args, :body; include Unparser; end
class Lamb < Struct.new :tyargs, :args, :body; include Unparser; end
class BinOp < Struct.new :fst, :op, :snd; include Unparser; end
class Hole < Struct.new; include Unparser; end
class Paren < Struct.new :value; include Unparser; end
