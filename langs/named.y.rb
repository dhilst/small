# Usage racc datatypes.y.rb && ruby datatypes.tab.rb
#
# Simple language with only named functions (no anonymous functions, no currying)

class Parser
  prechigh
    nonassoc "!"
    nonassoc "(" ")"
    nonassoc "&"
    nonassoc "."
    nonassoc ","
    right "->"
    nonassoc "[" "]"
    nonassoc "{" "}"
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
  stmt : fun | typ_decl

  typ_decl : "type" fqdn ":" typ { 
        OpenStruct.new(typ: :typ_decl, name: val[1], value: val[3]) }

  fqdn : WORD "." fqdn { [val[0], *val[2]] } | WORD 

  fun : "fun" WORD "(" args ")" ":" typ "=" expr
       { OpenStruct.new(typ: :fun, name: val[1], args: val[3], ret_typ: val[6],  body: val[8]) }
  fun : "fun" WORD "(" ")" ":" typ "=" expr
      { 
         t = val[5]
         # t = t.first unless t.is_a? Ctr
        OpenStruct.new(typ: :fun, name: val[1], args: [], ret_typ: t, body: val[7]) 
      }
  args : arg "," args { [val[0], *val[2]] } | arg { [val[0]] }
  arg : WORD ":" typ { [val[0], val[2]] }
  typ : typ "->" typ { 
        Ctr.new(:Arrow, [val[0], val[2]].flatten) }
      | "[" typ "]" typ { Ctr.new(:MethodCall, [val[1], val[3]]) }
      | "->" typ { Ctr.new(:Arrow, [val[1]]) }
      | "!" words { val[1].to_sym  }
      | words {
        if val.size == 1
          val[0]
        else
          val
        end
      }
  words : words WORD { [val[0], val[1]] } | WORD | "(" words ")" { val[1] }
  # typ : typ WORD | WORD | typ "->" typ | "(" typ ")"
  expr : if_ | do_ | let | expr_0
  expr_0 : call | expr_1
  expr_1 : atom

  let : "let" WORD ":" typ "=" expr "in" expr 
      # let x = y  in z ~> (fun x => z) y
      { OpenStruct.new(typ: :call, 
                       func: OpenStruct.new(typ: :fun, 
                                            name: "_let_#{object_id}", 
                                            args: [ [val[1].to_sym, val[3]] ],
                                            ret_typ: nil,
                                            body: val[7]),
                       args: [val[5]])
      }

  exprs_sc : expr ";" exprs_sc
  { [val[0], val[2]].flatten } 
  | expr ";" { [val[0]] }

  exprs : expr "," exprs 
  { [val[0], *val[2]] } 
  | expr { [val[0]] }

  do_ : "do" exprs_sc "end"
  { OpenStruct.new(typ: :call, func: :seq, args: val[1]) }

  call : expr "(" exprs ")"
       { OpenStruct.new(typ: :call, func: val[0], args: val[2]) }
       | expr "(" ")"
       { OpenStruct.new(typ: :call, func: val[0], args: []) }

  atom : INT | WORD | BOOL | STRING | NIL | method | list | hashtbl | as_block # this is not an "atom" anymore, rename it
  as_block : "&" WORD { OpenStruct.new(typ: :as_block, val: val[1]) }
  method : expr "." WORD { OpenStruct.new(typ: :call, func: :method, args: [val[0], val[2].to_s]) }
  list : "[" exprs "]" { val[1] }
       | "[" "]" { [] }
  hashtbl : "{" fields "}" { val[1].to_h }
          | "{" "}" { {} }
  fields : pair "," fields { [val[0], *val[2]] } | pair { [val[0]] }
  pair : expr "=>" expr { [val[0], val[2]] }
  if_ : "if" expr "then" expr "else" expr
       { OpenStruct.new(typ: :if_, cond: val[1],
                        then_: val[3], else_: val[5]) }
end

---- inner

KEYWORDS = %w(fun let in if then else true false do end nil type)
SYMBOLS = %w(; : => = ( ) , ! -> { } . [ ] & ").map { |x| Regexp.quote(x) }
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

---- header

require "pry"
require "ostruct"
require "boolean"

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
      when Class, NilClass, Module # Boolean is a Module not a Class
        x
      when Symbol
        begin
          Object.const_get(x)
        rescue
          x
        end
      else
        fail "flat : invalid argument --> #{x} : #{x.class}"
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
      when :typ_decl
        nil
      else
        eval_expr(stmt, env)
      end
    else
      eval_expr(stmt, env)
    end
  end

  def eval_expr(expr, env)
    case expr
    when Integer, Boolean, Method, Proc, String, NilClass
      expr
    when Hash
      expr.map {|k, v| [eval_expr(k, env), eval_expr(v, env)] }.to_h
    when Array
      expr.map {|elem| eval_expr(elem, env) }
    when Symbol
      if /[[:upper:]]/.match(expr)
        return Object.const_get(expr)
      end
      fail "unbounded variable #{expr}" unless env.key? expr
      env[expr]
    when OpenStruct
      case expr.typ
      when :call
        # This is a special case for handling the & operator
        # foo(&bar) pass bar as a block to foo
        if expr.args.size == 1 && expr.args[0].is_a?(OpenStruct) && expr.args[0].typ == :as_block
          f = eval_expr(expr.func, env)
          arg = eval_expr(expr.args[0].val, env)
          return f.call(&arg)
        end
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
        fail "bad expression ---> #{expr}"
      end
    end
  end
end

class TypRule
  def initialize(name, &block)
    @block = block
    @name = name
  end

  def run(typechecker, env, args)
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
  index: ->(ar, idx) { ar[idx] },
  method: ->(obj, m) { obj.method(m) }
}

class Typechecker
  def global_env
    {
      eq: Ctr.new(:Arrow, [Object, Object, Boolean]),
      seq: TypRule.new(:seq) do |typechecker, env, args|
        *args, last = args
        args.each do |arg|
          typechecker.typecheck_expr(arg, env)
        end
        typechecker.typecheck_expr(last, env)
      end,
      index: Ctr.new(:Arrow, [Object, Integer, Object]),
      puts: Ctr.new(:Arrow, [Object, NilClass]),
      add: Ctr.new(:Arrow, [Integer, Integer, Integer]),
      sub: Ctr.new(:Arrow, [Integer, Integer, Integer]),
      mul: Ctr.new(:Arrow, [Integer, Integer, Integer]),
      method: TypRule.new(:method) do |typechecker, env, args|
        obj, meth = args
        case obj
        when Symbol
          t = env[[obj, meth.to_sym]]
          t ||= env[obj]
          t
        else
          obj = typechecker.typecheck_expr(obj, env)
          obj = obj.to_s.to_sym if obj.is_a?(Class)
          t = env[[obj, meth.to_sym]]
        end
        fail "unbounded method method(#{obj}, \"#{meth}\")" \
             if t.nil?
        t 
      end,
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
        if ENV["ENABLE_RECURSION"]
          ftyp = Ctr.new(:Arrow, [*stmt.args.map {|x| x[1..]}, stmt.ret_typ].map(&Ctr.method(:normalize)))
          newenv = newenv.merge({ stmt.name => ftyp })
        end
        typs = stmt.args.map {|x| x[1..] }
        body = typecheck_expr(stmt.body, newenv)
        ret_typ = Ctr.normalize(stmt.ret_typ)
        do_typecheck(ret_typ, body, newenv, stmt, variance: :contravariant)
        env[stmt.name] = Ctr.new(:Arrow, [*typs, body])
      when :typ_decl
        fail "#{stmt.name} is already defined as #{env[stmt.name]}, refusing to override it" \
          if env.key?(stmt.name)
        env[stmt.name] = stmt.value
        nil
      else
        fail "bad stmt #{stmt}"
      end
    else
      fail "bad stmt 2 #{stmt}"
    end
  end

  def ret(expr, t)
    # puts("#{expr} : #{t}")
    t
  end

  def typecheck_expr(expr, env)
    case expr
    when OpenStruct 
      case expr.typ
      when :as_block
        ret(expr, typecheck_expr(expr.val, env))
      when :if_
        cond = typecheck_expr(expr.cond, env)
        fail "type error expected Boolean, found #{cond} #{cond.class}" \
          unless cond == Boolean
        then_ = typecheck_expr(expr.then_, env)
        else_ = typecheck_expr(expr.else_, env)
        do_typecheck(then_, else_, env, expr)
        ret(expr, then_)
      when :call
        f = typecheck_expr(expr.func, env)
        args = expr.args.map {|arg| Ctr.normalize(typecheck_expr(arg, env)) }
        case f
        when TypRule # this is for builtin functions with custom typechecking
          return ret(expr, f.run(self, env, expr.args))
        end
        fnorm = Ctr.normalize(f)
        case fnorm
        when Class
          if expr.func&.func == :method
            obj_sym, meth_str = expr.func.args
            obj = typecheck_expr(obj_sym, env)
            k = [obj, meth_str.to_sym]
            t = env[k]
            fail "unbounded method #{exr.func}" if t.nil?
            this_expected_type = t.args[0]
            method_type = t.args[1]
            do_typecheck(this_expected_type, obj, env, expr)
            targs = t.args[1].args[0..-2]
            fail "arity error, expected #{targs.size} but found #{expr.args.size}" \
              unless targs.size == expr.args.size
            args = expr.args.map {|x| typecheck_expr(x, env) }
            targs.zip(args).each do |a, b|
              do_typecheck(a, b, env, expr)
            end
            Ctr.normalize(t.args[1].args.last)
          else
            fail "todo"
          end
        when Ctr
          case fnorm.name
          when :MethodCall
            this_expected, typ = fnorm.args # (foo()) .read() ...  foo() : [this]
            fail "invalid argument" unless expr.func.is_a?(OpenStruct) && expr.func.typ == :call &&
                                           expr.func.func == :method
            this_real, funcargs = expr.func.args.map {|x| Ctr.normalize(typecheck_expr(x, env)) }
            do_typecheck(this_expected, this_real, env, expr)
            fargs = typ.args[..-2]
            fail "arity error, expected #{fargs.size} arguments, but found #{args.size} in #{expr}" \
              if fargs.size != args.size
            fargs.zip(args).each do |farg, arg|
              do_typecheck(farg, arg, env, expr)
            end
            return ret(expr, typ.args.last)
          when :Arrow
            fargs = fnorm.args[..-2]
            fail "arity error, expected #{fargs.size} arguments, but found #{args.size} in #{expr}" \
              if fargs.size != args.size
            fargs.zip(args).each do |farg, arg|
              do_typecheck(farg, arg, env, expr)
            end
            return ret(expr, fnorm.args.last)
          else
            fail "invalid Ctr, #{fnorm}"
          end
        else
          fail "typecheck_expr invalid function type #{fnorm}"
        end
      when :fun
        newenv = env.merge(expr.args.to_h)
        typs = expr.args.map {|x| x[1..] }
        tbody = typecheck_expr(expr.body, newenv)
        if expr.ret_typ.nil?
          expr.ret_typ = tbody
        else
          do_typecheck(tbody, expr.ret_typ)
        end

        ret(expr, Ctr.new(:Arrow, [*typs, tbody]))
      else
        fail "bad expr OpenStruct --> #{expr}"
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

  def do_typecheck(farg, arg, env, expr, variance: :covariant)
    case [farg, arg].map(&:class)
    when [Symbol, Class]
      do_typecheck(typecheck_expr(farg, env), arg, env, expr)
    when [Symbol, Symbol]
      do_typecheck(typecheck_expr(farg, env), typecheck_expr(arg, env), env, expr)
    when [Class, Symbol]
      do_typecheck(farg, typecheck_expr(arg, env), env, expr)
    when [Class, Class]
      case variance
      when :covariant
        fail "type error, expecting #{farg}, but found #{arg}, in #{expr}" unless arg <= farg
      when :contravariant
        fail "type error, expecting #{farg}, but found #{arg}, in #{expr}" unless arg >= farg
      else
        fail "do_typecheck : invalid variance #{variance}"
      end
    else
      fail "type error strict, expecting #{farg}, but found #{arg}, in #{expr}" unless arg == farg
    end
  end
end


ast = Parser.new.parse(<<END

type Hash.dig : [Hash] Integer -> String;

fun main() : NilClass =
    puts({0 => "Hello world"}.dig(0));
END
)
# pp ast
Typechecker.new.typecheck(ast)
Interpreter.new.run(ast, global_env)

