class Parser
  prechigh
    left '|>'
    left '*' '/'
    left '+' '-'
    left '='
  preclow
  token WORD INT TRUE FALSE UNIT STRING
  options no_result_var
  rule
  start: stmts { [val[0]].flatten }

  stmts : stmt_0 | stmt_0 ";" stmts { [val[0], val[2]] }
  stmt_0 : let_stmt | expr_0

  let_stmt : "let" WORD "=" expr_0 { LetStmt.new(val[1], val[3]) }
           | "let" "_" "=" expr_0 { LetStmt.new(:_, val[3]) }

  expr_0 : fun | funm | if_ | letin | expr_1
  expr_1 : bin | expr_5 
  expr_5 : app | expr_10
  expr_10 : atom

  if_ : "if" expr_0 "then" expr_0 "else" expr_0 { If.new(val[1], val[3], val[5]) }
  fun : "fun" WORD ":" typ_0 "=>" expr_0 { Fun.new(val[1], val[3], val[5]) }
  funm : "fun" funm_args "=>" expr_0 { funm_sugar(val[1].flatten, val[3]) }
  funm_args : funm_arg funm_args { [val[0], val[1]] } | funm_arg
  funm_arg : "(" WORD ":" typ_0 ")" { Arg.new(val[1], val[3]) }
  app : expr_5 expr_10 { App.new(val[0], val[1]) }
  bin : expr_1 "+" expr_1 { Bin.new(:+, val[0], val[2]) }
      | expr_1 "-" expr_1 { Bin.new(:-, val[0], val[2]) }
      | expr_1 "*" expr_1 { Bin.new(:*, val[0], val[2]) }
      | expr_1 "/" expr_1 { Bin.new(:"/", val[0], val[2]) }
      | expr_1 "=" expr_1 { Bin.new(:"==", val[0], val[2]) }
      | expr_1 "|>" expr_1 { App.new(val[2], val[0]) }
  atom : WORD { val[0].to_sym } | const | hole | "()" { :unit } | "(" expr_0 ")" { val[1] } | list
  list : "[]" | "[" items "]" { [val[1]].flatten }
  items : expr_0 | expr_0 "," items { [val[0], val[2]] }
  const : INT | TRUE { true } | FALSE { false } | UNIT | STRING
  letin : "let" WORD "=" expr_0 "in" expr_0 { App.new(Fun.new(val[1], nil, val[5]), val[3]) }
  hole : "?" { :question } | "_" { :under }

  typ_0 : t_arrow | typ_1
  typ_1 : t_app | typ_2
  typ_2 : t_atom

  t_app : typ_1 typ_2
  t_atom : t_const | "(" typ_0 ")" { val[1] }
  t_const : "int" { :t_int } | "list" typ_2 { [:t_list, val[1]] } | "_" { :t_under }
  t_arrow : typ_1 "->" typ_0 { [:t_arrow, val[0], val[2]] }
end

---- inner

CONSTS = %w[true false unit]
KEYWORDS = %w[def fun int if then else list let in]
SYMBOLS = %w(=> |> () = [ ] ( ) : -> + - * / ; , ? $ _)
            .map { |x| Regexp.quote(x) }

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
  return acc.join("")
end

def tokenize(str)
  require 'strscan'
  result = []
  s = StringScanner.new(str)
  until s.empty?
    case
    when s.scan(/\s+/)
    when s.scan(/#/)
      s.skip_until(/$/)
    when tok = s.scan(/\b(#{CONSTS.join("|")})\b/)
      result << [tok.upcase.to_sym, tok.to_sym]
    when tok = s.scan(/\b(#{KEYWORDS.join("|")})\b/)
      result << [tok, nil]
    when tok = s.scan(/#{SYMBOLS.join("|")}/)
      result << [tok, nil]
    when tok = s.scan(/\d+/)
      result << [:INT, tok.to_i]
    when tok = s.scan(/\w+((\.|::)\w+)*/)
      result << [:WORD, tok]
    when tok = s.scan(/"/)
      result << [:STRING, readstring(s)]
    else
      fail "bad token #{s.peek 10}"
    end
  end
  result << [false, false]
  result
end

def parse(str)
  @tokens = tokenize(str)
  Interpreter.new(do_parse)
end

def next_token
  @tokens.shift
end

def funm_sugar(args, body)
  last, *args = args.reverse
  init = Fun.new(last.arg, last.typ, body)
  args.reduce(init) do |acc, arg|
    Fun.new(arg.arg, arg.typ, acc)
  end
end

---- header
class Fun < Struct.new :arg, :typ, :body; end
class Arg < Struct.new :arg, :typ; end
class App < Struct.new :f, :arg; end
class If < Struct.new :cond, :then_, :else_; end
class Bin < Struct.new :op, :a, :b; end
class LetStmt < Struct.new :name, :value; end

class Interpreter
  attr_accessor :ast
  def initialize(ast)
    @ast = ast
  end

  def eval
    eval_stmts(@ast, {})
  rescue => e
    raise if ENV["ADVLANG_DEBUG"]
    puts "Error: #{e}"
  end

  private

  def eval_stmts(exprs, env)
    exprs.each do |expr|
      eval_stmt(expr, env)
    end
  end

  def eval_stmt(stmt, env)
    case stmt
    when LetStmt
      value = eval_expr(stmt.value, env)
      env[stmt.name.to_sym] = value
    else
      eval_expr(stmt, env)
    end

    nil
  end

  def eval_expr(expr, env)
    case expr
    when Integer, String, TrueClass, FalseClass
      return expr
    when Array
      expr.map {|item| eval_expr(item, env) }
    when Fun
      return ->(x) { eval_expr(expr.body, env.merge({ expr.arg.to_sym => x })) }
    when If
      if eval_expr(expr.cond, env)
        eval_expr(expr.then_, env)
      else
        eval_expr(expr.else_, env)
      end
    when Symbol
      return expr if [:unit].include?(expr)

      if env.key?(expr)
        env[expr]
      else
        sym = expr.to_s
        begin
          if sym.include? "."
            namespace, _, name = sym.partition(".").map(&:to_sym)
            const = Object.const_get(namespace)
            x = const.instance_methods.include?(name)
            if const.respond_to?(name)
              result = const.method(name)
            elsif const.instance_methods.include?(name)
              result = Proc.new {|x| const.instance_method(name).bind(x) }.curry
            else
              fail "unbounded variable #{expr}"
            end
          else
            result = Kernel.method(sym).curry
          end
        rescue NameError => e
          fail "unbounded variable #{expr}"
        end

        result
      end
    when App
      case expr.f
      when Symbol
        f = eval_expr(expr.f, env)
        eval_expr(App.new(f, expr.arg), env)
      when Fun
        arg = eval_expr(expr.arg, env)
        f = eval_expr(expr.f, env)
        f.call(arg)
      when Proc, Method
        arg = eval_expr(expr.arg, env)
        expr.f.call(arg)
      when App
        f = eval_expr(expr.f, env)
        eval_expr(App.new(f, expr.arg), env)
      else
        fail "bad application, did you forgot a ';'? #{expr}"
      end
    when Bin
      eval_bin_expr(expr.op, expr.a, expr.b, env)
    else
      fail "unknown expression #{expr}"
    end
  end

  def eval_bin_expr(op, a, b, env)
    a = eval_expr(a, env)
    b = eval_expr(b, env)
    eval_expr(a.send(op, b), env)
  end
end

---- footer
# interp = Parser.new.parse(<<END
# puts (if true then 1 else 0);
# def x = 100;
# puts x;

# # lets try some requests
# require "uri";
# require "net/http";
# def uri = URI("http://google.com");
# puts uri;
# p (Net::HTTP.get_response uri);
# (fun x : list (int -> int) => p x) 1;
# p [1,2,3,4]
# END
# )
# interp.ast.each(&method(:puts))
# interp.eval

Parser.new.parse(ARGF.read).eval
