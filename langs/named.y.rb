# Usage racc datatypes.y.rb && ruby datatypes.tab.rb
#
# Simple language with only named functions (no anonymous functions, no currying)

class Parser
  prechigh
    nonassoc "!"
    nonassoc "(" ")"
    right "->"
    left "*" "/"
    left "+" "-"
    nonassoc "true" "false" "nil"
    nonassoc "if" "then" "else"
    nonassoc "let" "=" "in"
  preclow
  token WORD INT BOOL STRING NIL
  options no_result_var

  start main

  rule

  main : stmts
  
  stmts : stmt ";" stmts { 
          [val[0], val[2]].flatten } 
        | stmt ";" { [val[0]] }
  stmt : fun

  fun : "fun" WORD "(" args ")" ":" typ "=" expr
       { OpenStruct.new(typ: :fun, name: val[1], args: val[3], ret_typ: val[6].first,  body: val[8]) }
  fun : "fun" WORD "(" ")" ":" typ "=" expr
      { 
         t = val[5]
         t = t.first unless t.is_a? Ctr
        OpenStruct.new(typ: :fun, name: val[1], args: [], ret_typ: t, body: val[7]) 
      }
  args : arg "," args { [val[0], *val[2]] } | arg { [val[0]] }
  arg : WORD ":" typ { [val[0], val[2]] }
  typ : typ "->" typ { 
        Ctr.new(:Arrow, [val[0], val[2]].flatten) }
      | "!" words { "!#{val[1]}".to_sym }
      | words {
        if val[0].size == 1
          val[0]
        else
          val
        end
      }
  words : words WORD { [val[0], val[1]] } | WORD | "(" words ")" { val[1] }
  # typ : typ WORD | WORD | typ "->" typ | "(" typ ")"
  expr : if_ | do_ | expr_0
  expr_0 : call | expr_1
  expr_1 : atom

  exprs_sc : expr ";" exprs_sc
  { [val[0], val[2]].flatten } 
  | expr ";" { [val[0]] }

  exprs : expr "," exprs 
  { [val[0], val[2]].flatten } 
  | expr { [val[0]] }

  do_ : "do" exprs_sc "end"
  { OpenStruct.new(typ: :call, func: :seq, args: val[1]) }

  call : expr "(" exprs ")"
       { OpenStruct.new(typ: :call, func: val[0], args: val[2]) }
       | expr "(" ")"
       { OpenStruct.new(typ: :call, func: val[0], args: []) }

  atom : INT | WORD | BOOL | STRING | NIL
  if_ : "if" expr "then" expr "else" expr
       { OpenStruct.new(typ: :if_, cond: val[1],
                        then_: val[3], else_: val[5]) }
end

---- inner

KEYWORDS = %w(fun let in if then else true false do end nil)
SYMBOLS = %w(; : = ( ) , ! -> ").map { |x| Regexp.quote(x) }
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
    when tok = s.scan(/"/)
      x = readstring(s)
      result << [:STRING,x]
    when tok = s.scan(/(#{SYMBOLS.join("|")})/)
      result << [tok, nil]
    when tok = s.scan(/\b(#{KEYWORDS.join("|")})\b/)
      case tok
      when "true"
        result << [:BOOL, true]
      when "false"
        result << [:BOOL, false]
      when "nil"
        result << [:NIL, nil]
      else
        result << [tok, nil]
      end
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

def of_typ(str)
  if str.size == 1
    UVar.new(str)
  else
    UFun.new(str, [])
  end
end

---- header

require "pry"
require "ostruct"

class Array
  def unwrap
    return first if size == 1
    self
  end
end

class Ctr < Struct.new :name, :args
  class << self

    def normalize(x)
      flat(x)
    end

    def ==(other)
      fail "Ctr.== invalid argument #{other}" unless other.is_a? Ctr
      name == other.name &&
        args.size == other.args.size &&
        args.zip(other.args).all {|a,b| a == b}
    end

    private 

    def is_nested_arrow?(x)
      fail "is_nested_arrow : invalid type #{x}" unless x.is_a? Ctr

      x.name == :Arrow &&
        x.args.size == 2 &&
        x.args[1].is_a?(Ctr) &&
        x.args[1].name == :Arrow
    end

    def flat(x)
      # Arrow (x, Arrow (y, z))
      # Ctrn.new(:Arrow, [x, Ctr.new(:Arrow, [y, z])])
      case x
      when Array
        if x[1].is_a?(Ctr) && x[1].name == :Arrow
          [x[0], *x[1].args.flatten.map(&method(:flat))].unwrap
        else
          x.map(&method(:flat)).unwrap
        end
      when Ctr
        if is_nested_arrow?(x)
          args = [*x.args[0], *x.args[1].args].flatten
          args = args.map(&method(:flat))
          Ctr.new(:Arrow, args)
        else
          Ctr.new(x.name, x.args.map(&method(:flat)))
        end
      when Class
        x
      when Symbol
        begin
          Object.const_get(x)
        rescue
          x
        end
      else
        fail "flat : invalid argument #{x}"
      end
    end
    
    def hydrate(x)
      case x
      when Symbol
        begin
          Object.const_get(x)
        rescue StandardError
          x
        end
      when Ctr
        Ctr.new(x.name, x.args.flatten.map {|arg| hydrate(arg) })
      when NilClass
        nil
      when Class
        x
      else
        fail "hydrate : invalid arguent #{x.class} #{x}"
      end
    end
  end
end


---- footer

class Interpreter
  def run(stmts, env)
    stmts.map do |stmt|
      eval_stmt(stmt, env)
    end
    
    return unless env.key? :main

    main = env[:main]
    eval_expr(OpenStruct.new(typ: :call, func: main, args: []), env)
  end

  def eval_stmt(stmt, env)
    case stmt
    when OpenStruct
      case stmt.typ
      when :fun
        env[stmt.name] = eval_expr(stmt, env)
      else
        eval_expr(stmt, env)
      end
    else
      eval_expr(stmt, env)
    end
  end

  def eval_expr(expr, env)
    case expr
    when Integer, TrueClass, FalseClass, Method, Proc, String, NilClass
      expr
    when Symbol
      if /[[:upper:]]/.match(expr)
        return Object.const_get(expr)
      end
      fail "unbounded variable #{expr}" unless env.key? expr
      env[expr]
    when OpenStruct
      case expr.typ
      when :call
        f = eval_expr(expr.func, env)
        args = expr.args.map {|x| eval_expr(x, env) }
        fail "bad application #{f}" unless [Method, Proc].member? f.class
        f.call(*args)
      when :fun
        ->(*args) {
          expr_args = expr.args.map(&:first)
          fail "arity error in #{args} <> #{expr.args}" \
            unless args.size == expr_args.size
          newenv = env.merge(expr_args.zip(args).to_h)
          eval_expr(expr.body, newenv)
        }
      when :if_
        if eval_expr(expr.cond, env)
          eval_expr(expr.then_, env)
        else
          eval_expr(expr.else_, env)
        end
      else
        fail "bad expression #{expr}"
      end
    end
  end
end

class TypRule
  def initialize(name, &block)
    @block = block
    @name = name
  end

  def run(typechecker, env, *args)
    @block.call(typechecker, env, args)
  end
end

global_env = {
  puts: method(:puts),
  add: ->(a, b) { a + b },
  sub: ->(a, b) { a - b },
  mul: ->(a, b) { a * b },
  eq: ->(a, b) { a == b },
  seq: ->(*args) { args&.last },
  method: ->(obj, m) { obj.method(m) }
}

class Typechecker
  def global_env
    {
      seq: TypRule.new(:seq) do |typechecker, args, env|
        *args, last = args
        args.each do |arg|
          typechecker.typecheck_expr(arg, env)
        end
        x = typechecker.typecheck_expr(last, env)
        x
      end,
      puts: Ctr.new(:Arrow, [Object, NilClass]),
      add: Ctr.new(:Arrow, [Integer, Integer, Integer]),
      method: Ctr.new(:Arrow, [Object, String, Object]),
    }
  end

  def typecheck(stmts)
    env = global_env
    stmts.map do |stmt|
      typecheck_stmt(stmt, env)
    end
  end

  def typecheck_stmt(stmt, env)
    case stmt
    when OpenStruct
      case stmt.typ
      when :fun
        newenv = env.merge(stmt.args.to_h)
        typs = stmt.args.map {|x| x[1..] }
        body = typecheck_expr(stmt.body, newenv)
        ret_typ = Ctr.normalize(stmt.ret_typ)
        do_typecheck(ret_typ, body, newenv, stmt)
        env[stmt.name] = Ctr.new(:Arrow, [*typs, body])
      else
        fail "bad stmt #{stmt}"
      end
    else
      fail "bad stmt 2 #{stmt}"
    end
  end

  def typecheck_expr(expr, env)
    case expr
    when OpenStruct 
      case expr.typ
      when :call
        f = typecheck_expr(expr.func, env)
        args = expr.args.map {|arg| Ctr.normalize(typecheck_expr(arg, env)) }
        case f
        when TypRule # this is for builtin functions with custom typechecking
          return f.run(self, args, env)
        end
        fnorm = Ctr.normalize(f)
        fargs = fnorm.args[..-2]
        fail "arity error, expected #{fargs.size} arguments, but found #{args.size} in #{expr}" \
          if fargs.size != args.size

        fargs.zip(args).each do |farg, arg|
          do_typecheck(farg, arg, env, expr)
        end
        fnorm.args.last
      when :fun
        newenv = env.merge(stmt.args.to_h)
        typs = stmt.args.map {|x| x[1..] }
        tbody = typecheck_expr(expr.body, newenv)
        Ctr.new(:Arrow, [*typs, tbody])
      else
        fail "bad expr OpenStruct #{expr}"
      end
    when Symbol
      if env.key? expr
        env[expr]
      elsif expr.to_s[0].match /[[:upper:]]/
        begin
          Object.const_get(expr)
        rescue StandardError
          fail "unbounded variable #{expr}"
        end
      else
        fail "unbounded variable #{expr}"
      end
    when Class
      expr
    else
      expr.class
    end
  end


  def do_typecheck(farg, arg, env, expr)
    case [farg, arg].map(&:class)
    when [Symbol, Class]
      do_typecheck(typecheck_expr(farg, env), arg, env, expr)
    when [Symbol, Symbol]
      do_typecheck(typecheck_expr(farg, env), typecheck_expr(arg, env), env, expr)
    when [Class, Symbol]
      do_typecheck(farg, typecheck_expr(arg, env), env, expr)
    when [Class, Class]
      fail "type error, expecting #{farg}, but found #{arg}, in #{expr}" unless arg <= farg
    else
      return nil if farg == Object
      fail "type error strict, expecting #{farg}, but found #{arg}, in #{expr}" unless arg == farg
    end
  end
end


ast = Parser.new.parse(<<END

fun f() : Object -> NilClass = puts;

fun main() : NilClass = do
    puts(method(nil, "class")());
end;
END
)
# pp ast
Typechecker.new.typecheck(ast)
Interpreter.new.run(ast, global_env)
