# Usage racc datatypes.y.rb && ruby datatypes.tab.rb
#
# Simple ML like language using Scott encoding

class Parser
  token WORD INT BOOL
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
       | "fun" WORD ":" WORD "=>" expr_0 { Lamb.new(val[1], of_typ(val[3]), val[5]) }
  app : expr_1 expr_2 { App.new(val[0], val[1]) }
  atom : WORD | const | "(" expr_0 ")" { val[1] }
  const : INT | BOOL
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

class DataType < Struct.new :name, :args, :ctrs; def to_s; Unparser.new.unparse([self]); end; end
class Ctr < Struct.new :name, :args; def to_s; Unparser.new.unparse([self]); end; end
class App < Struct.new :f, :arg; def to_s; Unparser.new.unparse([self]); end; end
class Let < Struct.new :x, :e1, :e2; def to_s; Unparser.new.unparse([self]); end; end
class Lamb < Struct.new :arg, :typ, :body; def to_s; Unparser.new.unparse([self]); end; end
class Val < Struct.new :name, :value; def to_s; Unparser.new.unparse([self]); end; end
class Match < Struct.new :scrutinee, :patterns; def to_s; Unparser.new.unparse([self]); end; end
class MatchPattern < Struct.new :pat, :body; def to_s; Unparser.new.unparse([self]); end; end
class If < Struct.new :cond, :then_, :else_; def to_s; Unparser.new.unparse([self]); end; end

---- footer

require 'pry'

# Receives an AST and return a simpler AST with only
# Val, App, Lamb, Symbol (denoting variables) and constants
class Desuger
  def desugar(stmts)
    stmts.map(&method(:desugar_stmt)).flatten
  end

  private

  def lamb(*args_body)
    *args, arg, body = args_body
    init = Lamb.new(arg, nil, body)
    args.reverse.reduce(init) do |acc, arg|
      Lamb.new(arg, nil, acc)
    end
  end

  def app(*exprs)
    e1, e2, *exprs = exprs
    init = App.new(e1, e2)
    exprs.reduce(init) do |acc, arg|
      App.new(acc, arg)
    end
  end

  def desugar_stmt(stmt)
    case stmt
    when DataType
      ctrs = stmt.ctrs.map(&:name)
      stmt.ctrs.map.with_index do |ctr, idx|
        if ctr.args.nil?
          # none ~> let none = fun some => fun none => none
          Val.new(ctr.name, lamb(*[*ctrs, ctr.name]))
        else
          # some x ~ let some = fun x => fun some => fun none => some x
          Val.new(ctr.name, lamb(*[*ctr.args, *ctrs, app(ctr.name, *ctr.args)]))
        end
      end
    when Val
      Val.new(stmt.name, desugar_expr(stmt.value))
    else
      desugar_expr(stmt)
    end
  end

  def desugar_expr(expr)
    case expr
    when Integer, Symbol, TrueClass, FalseClass, If
      expr
    when App
      App.new(desugar_expr(expr.f), desugar_expr(expr.arg))
    when Lamb
      Lamb.new(expr.arg, expr.typ, desugar_expr(expr.body))
    when Let
      # let x = e1 in e2 ~> (fun x => e2) e1
      App.new(
        Lamb.new(expr.x, nil, desugar_expr(expr.e2)),
        desugar_expr(expr.e1))
    when Match
      # match some x with | some y => y | none => z
      # ~>
      # (some x) (fun y => y) z
      branches = expr.patterns.map do |pat|
        case pat.pat
        when Symbol
          # none => ... ~> ...
          pat.body
        when Array
          # some x => ... ~> fun x => ...
          # pair a b => ... ~> fun a => fun b => ...
          _, *args = pat.pat
          lamb(*args, pat.body)
        else
          fail "bad match branch #{pat} in #{expr}"
        end
      end
      app(expr.scrutinee, *branches)
    else
      fail "desugar error : bad expr #{expr}"
    end
  end
end

class Unparser
  def unparse(stmts)
    stmts.map(&method(:unparse_stmt)).join(";\n\n")
  end

  private

  def ident(i, str)
    str.split("\n").map do |str|
      "#{' ' * i}#{str}"
    end.join("\n")
  end

  def unparse_stmt(stmt)
    case stmt
    when DataType
      case stmt.args
      when Array
        "data #{stmt.name} #{stmt.args.join(' ')} = #{unparse_ctrs(stmt.ctrs)}"
      when NilClass
        "data #{stmt.name} = #{unparse_ctrs(stmt.ctrs)}"
      end
    when Val
      "val #{stmt.name} =\n#{ident(2, unparse_expr(stmt.value))}"
    else
      unparse_expr(stmt)
    end
  end

  def unparse_ctrs(ctrs)
    ctrs.map(&method(:unparse_ctr)).join(" | ")
  end

  def unparse_ctr(ctr)
    fail "unparse error : not a ctr #{ctr}" unless ctr.is_a? Ctr
    "#{ctr.name} #{ctr.args&.join(' ')}"
  end

  def unparse_expr(expr)
    case expr
    when Integer, Symbol, TrueClass, FalseClass
      expr.to_s
    when Let
      "let #{expr.x} = #{unparse_expr(expr.e1)} in #{unparse_expr(expr.e2)}"
    when Lamb
      "fun #{expr.arg} => #{unparse_expr(expr.body)}"
    when App
      case expr.arg
      when App, Lamb, Let
        "#{unparse_expr(expr.f)} (#{unparse_expr(expr.arg)})"
      else
        case expr.f
        when Lamb
          "(#{unparse_expr(expr.f)}) #{unparse_expr(expr.arg)}"
        else
          "#{unparse_expr(expr.f)} #{unparse_expr(expr.arg)}"
        end
      end
    when Match
      "match #{unparse_expr(expr.scrutinee)} with\n" +
        unparse_match_patterns(expr.patterns)
    when If
      "if #{unparse_expr(expr.cond)}\n" +
        "then #{unparse_expr(expr.then_)}\n" +
        "else #{unparse_expr(expr.else_)}"
    else
      fail "unparse error : bad expression #{expr}"
    end
  end

  def unparse_match_patterns(patterns)
    patterns.map(&method(:unparse_match_pattern)).join("\n") + "\nend"
  end

  def unparse_match_pattern(pattern)
    case pattern.pat
    when Symbol
      "| #{pattern.pat} => #{unparse_expr(pattern.body)}"
    when Array
      "| #{pattern.pat.join(' ')} => #{unparse_expr(pattern.body)}"
    else
      fail "bad pattern pat #{pattern}"
    end
  end
end

class UFun < Struct.new :name, :args
  def to_s
    return "#{name}" if args.empty?

    case name
    when :arrow
      fail "invalid arrow it should have exactly 2 arguments, but found #{args}" if args.size != 2
      if args[0].is_a?(UFun) and args[0].name == :arrow
        "(#{args[0]}) -> #{args[1]}"
      else
        "#{args[0]} -> #{args[1]}"
      end
    else
      "#{name} #{args.join(' ')}"
    end
  end
end

class UVar
  @@next_letter = "a"

  attr_reader :letter

  def initialize(letter)
    @letter = letter.dup
  end

  def to_s
    "#{@letter}"
  end

  def self.fresh!
    l = @@next_letter
    @@next_letter.next!
    UVar.new(l)
  end

  def self.reset
    @@next_letter = "a"
  end

  def ==(b)
    fail "invalid comparison #{self} == #{b}" unless b.is_a? UVar
    @letter == b.letter
  end
end

class Unifier
  def self.unify(problems)
    return [] if problems.empty?
    p, *problems = problems
    a, b = p
    case [a,b].map(&:class)
    when [UVar, UVar]
      if a == b
        unify(problems)
      else
        problems = problems.map do |k, v|
          [subst(a, b, k), subst(a, b, v)]
        end
        [[a, b]] + unify(problems)
      end
    when [UFun, UVar]
      unify([[b, a]] + problems) # swap
    when [UFun, UFun]
      fail "unification error #{a} <> #{b}" if a.name != b.name or a.args.size != b.args.size
      unify(a.args.zip(b.args) + problems)
    when [UVar, UFun]
      fail "unification error #{a} occurs in #{b}" if occurs(a, b)
      problems = problems.map do |k, v|
        [subst(a, b, k), subst(a, b, v)]
      end
      [[a, b]] + unify(problems)
    else
      fail "invalid argument #{a.class} #{b.class}"
    end
  end

  def self.subst_env(subs, env)
    env.map do |k, v|
      [k, substm(subs, v)]
    end.to_h
  end

  def self.substm(subs, term)
    subs.reduce(term) do |term, s|
      k, v = s
      subst(k, v, term)
    end
  end

  def self.subst(k, v, term)
    case term
    when UFun
      UFun.new(term.name, term.args.map {|arg| subst(k, v, arg)})
    when UVar
      return v if term == k
      term
    end
  end

  def self.occurs(a, b)
    fail "invalid argument #{a} #{b}" unless a.is_a? UVar
    case b
    when UVar
      a == b
    when UFun
      b.args.any? do |barg|
        occurs(a, barg)
      end
    else
      fail "invalid argument, #{b}"
    end
  end
end

class TypeScheme < Struct.new :args, :typ
  def instantiate
    fresh_vars = args.map do |arg|
      [arg, UVar.fresh!]
    end
    Unifier.substm(fresh_vars, typ)
  end

  def self.generalize(typ, env)
    vs = vars(typ).reject {|v| env.has_value? v}
    TypeScheme.new(vs, typ)
  end

  def self.vars(typ)
    case typ
    when UVar
      [typ]
    when UFun
      typ.args.map do |arg|
        vars(arg)
      end.flatten.uniq.sort_by(&:to_s)
    else
      fail "invalid argument #{typ}"
    end
  end

  def to_s
    return typ.to_s if args.empty?
    "forall #{args.join(' ')} . #{typ}"
  end
end

class Typechecker
  def typecheck(stmts)
    env = global_env
    stmts.each do |stmt|
      UVar.reset
      stmt = typecheck_stmt(stmt, env)
      stmt
    end
  end

  private

  def arrow(*args)
    *args, a, b = args
    init = UFun.new(:arrow, [a, b])
    args.reverse.reduce(init) do |acc, arg|
      UFun.new(:arrow, [arg, acc])
    end
  end

  def global_env
    int = UFun.new(:int, [])
    nilt = UFun.new(:nil, [])
    bool = UFun.new(:bool, [])
    a = UVar.fresh!
    b = UVar.fresh!
    env = {
      unify: TypeScheme.new([a], arrow(a, a, a)),
      eq: TypeScheme.new([a], arrow(a, a, bool)),
      sub: TypeScheme.new([], arrow(int, int, int)),
      add: TypeScheme.new([], arrow(int, int, int)),
      mul: TypeScheme.new([], arrow(int, int, int)),
      puts: TypeScheme.new([a], arrow(a, nilt)),
    }
    env[:fix] = TypeScheme.new([a, b], arrow(arrow(arrow(a, b), a, b), a, b)) \
                              if ENV["ENABLE_FIXPOINT"]
    env
  end

  def typecheck_stmt(stmt, env)
    case stmt
    when Val
      t, val, s = typecheck_expr(stmt.value, env)
      t = Unifier.substm(s, t)
      t = TypeScheme.generalize(t, env)
      env[stmt.name] = t
      puts "#{stmt} : #{t}"
      Val.new(stmt.name, val)
    else
      t, stmt, s = typecheck_expr(stmt, env)
      t = Unifier.substm(s, t)
      t = TypeScheme.new([], t)
      puts "#{stmt} : #{t}"
      stmt 
    end
  end

  def typecheck_expr(expr, env)
    case expr
    when String, NilClass
      name = expr.class.name.downcase.sub(/class/, "")
      [UFun.new(name, []), expr, []]
    when Integer
      [UFun.new(:int, []), expr, []]
    when TrueClass, FalseClass
      [UFun.new(:bool, []), expr, []]
    when Symbol
      fail "unbound variable #{expr}" unless env.key? expr
      [env[expr].instantiate, expr, []]
    when Lamb
      if expr.typ
        targ = expr.typ
      else
        targ = UVar.fresh!
      end
      newenv = env.merge({ expr.arg => TypeScheme.new([], targ) })
      tbody, body, sbody = typecheck_expr(expr.body, newenv)
      typ = UFun.new(:arrow, [targ, tbody])
      typ = Unifier.substm(sbody, typ)
      lamb = Lamb.new(expr.arg, typ.args[0], body)
      [typ, lamb, sbody]
    when App
      tfunc, f, sfunc = typecheck_expr(expr.f, env)
      targ, arg, sarg = typecheck_expr(expr.arg, env)
      tfunc2 = UFun.new(:arrow, [targ, UVar.fresh!])
      sfunc2 = unify(expr, [[tfunc, tfunc2]] + sfunc + sarg)
      tresult = Unifier.substm(sfunc2, tfunc2)
      app = App.new(f, arg)
      [tresult.args[1], app, sfunc2]
    when If
      tcond, cond, scond = typecheck_expr(expr.cond, env)
      Unifier.unify([[tcond, UFun.new(:bool, [])]])
      tthen, then_, sthen = typecheck_expr(expr.then_, env)
      telse, else_, selse = typecheck_expr(expr.else_, env)
      sthenelse = unify(expr, [[tthen, telse]] + scond + sthen + selse)
      tif = Unifier.substm(sthenelse, tthen)
      if_ = If.new(cond, then_, else_)
      [tif, if_, sthenelse]
    else
      # PS in [let x = ... in ...], [x] is not universally
      # quantified. [let] is just sugar for application, only [val x =
      # ...] constructs are universally quantified.
      fail "invalid argument #{expr}"
    end
  end

  def unify(expr, args)
    Unifier.unify(args)
  rescue StandardError => e
    raise e unless e.to_s.include?("unification error")
    fail "type error #{e} in `#{expr}'"
  end
end

class Interpreter
  def eval(stmts)
    eval_stmts(stmts, global_env)
  end

  private

  def fix(f, x)
    fixm = method(:fix).curry
    f.call(fixm.call(f)).call(x)
  end

  def global_env
    {
      unify: ->(a, b){ b }.curry,
      puts: method(:puts),
      fix: method(:fix).curry,
      add: ->(a, b) { a + b }.curry,
      mul: ->(a, b) { a * b }.curry,
      sub: ->(a, b) { a - b }.curry,
      eq: ->(a, b) { a == b }.curry,
    }
  end

  def eval_stmts(stmts, env)
    stmts.each do |stmt|
      eval_stmt(stmt, env)
    end
  end

  def eval_stmt(stmt, env)
    case stmt
    when Val
      fail "bad name #{stmt.name} in #{stmt}" unless stmt.name.is_a? Symbol
      env[stmt.name] = stmt.value
    else
      eval_expr(stmt, env)
    end
  end

  def eval_expr(expr, env)
    case expr
    when App
      f = eval_expr(expr.f, env)
      arg = eval_expr(expr.arg, env)
      case f
      when Proc, Method
        eval_expr(f.call(arg), env)
      else
        fail "bad application #{expr}"
      end
    when Lamb
      ->(x) { eval_expr(expr.body, env.merge({expr.arg => x})) }
    when Symbol
      fail "Unbounded symbol #{expr}" unless env.key? expr
      eval_expr(env[expr], env)
    when If
      cond = eval_expr(expr.cond, env)
      if cond
        eval_expr(expr.then_, env)
      else
        eval_expr(expr.else_, env)
      end
    when Method, Proc, Integer, String, NilClass, TrueClass, FalseClass # puts return nil
      expr
    else
      fail "bad expression #{expr.class} #{expr}"
    end
  rescue StandardError => e
    puts "error with #{expr}"
    raise e
  end
end

code = <<END
val some = fun x => fun some => fun none =>
  unify none (some x);
val none = fun some => fun none =>
  unify some (fun _ => none);

match some 1 with
| some x => true
| none => false
end;

val ok = fun x => fun ok => fun err =>
  unify err (fun _ => ok x);

val err = fun x => fun ok => fun err =>
  unify ok (fun _ => err x);

match ok 1 with
| ok x => true
| error y => false
end;

match err true with
| ok x => puts x
| error y => puts y
end;

val bool_int = fun x => fun y => fun pair =>
    pair (unify true x) (unify 0 y);

val as_int = unify 0;
val as_bool = unify true;

fun x =>
  if x then x else 0
  # this is wrong, it should be a type error
  # x should have type int, and it's
  # being used in if conditional position wich
  # have to be bool
END

ast = Desuger.new.desugar(Parser.new.parse(code))
puts "Typechecking\n\n"
Typechecker.new.typecheck(ast)

puts "\n\nEvaluating\n\n"
Interpreter.new.eval(ast)
