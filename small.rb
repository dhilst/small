require "pry"
require "set"
require "readline"
require "fileutils"
require "./parser"

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
  
  def typ_args_in_common(data, ctr)
    fail "invalid argument not a data type" unless data.is_a? DataType
    fail "invalid argument not a ctr" unless ctr.is_a? Ctr

    Set[data.args] - Set[ctr.args]
  end

  def desugar_stmt(stmt)
    case stmt
    when DataType
      # data opt a = some a | none
      # --------------------------
      # val some = fun x : b -> a => fun none : a => some x
      # val none = fun some x : b -> a => fun none : a => none
      #
      # data ok a b = ok a | err b
      # --------------------------
      # val ok = fun x : b => fun ok : b -> a => fun err : c -> a => ok x
      # val err = fun x : c => fun ok : b -> a => fun err : c -> a => err x

      # val ok = fun x : b => fun ok : b -> a => fun err : c -> a => ok x

      # data ok2 a b c = ok a b => err c
      # ------------------------------------
      # val ok2 = 
      #   fun a : a => fun b : b =>
      #   fun ok : a -> b -> d => 
      #   fun err : c -> d => ok a b
      # 
      # 1. generate a fresh var for each constructor argument
      # 2. if the constructor as no argument generate a fresh var for it
      # 3. generate a fresh var for the conclusion of the type
      #    (d in the above example)
      # 4. generate the function [fun a : a => fun b : b => ...]
      #    these are the arguments for the current constructor
      #    a, b, .. are the variables generated in 1 and 2
      # 5. generate the function [fun ok : a -> b -> d => fun err : c -> d => ...]
      #    these are the constructors themselves
      # 6. generate the body, which is [app (ctr, *ctr_args)],
      #    i.e., the application of the current constructor with its arguments
      # 7. replace ... with the result of 5 in in 4
      # 8. replace .. with the result with the function body from 6 in 5
      fvs = FreshVars.new
      targs = stmt.args
      tctrs = stmt.ctrs.map do |ctr|
        args = targs&.select {|x| ctr.args&.include? x}
        [ctr, args&.flatten]
      end


      ctrs = stmt.ctrs.map(&:name)
      stmt.ctrs.map do |ctr|
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
    when Integer, Symbol, TrueClass, FalseClass, If, String, TypIntro
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
    when String
      expr.dump
    when Let
      "let #{expr.x} = #{unparse_expr(expr.e1)} in #{unparse_expr(expr.e2)}"
    when TypScheme
      "forall #{expr.var} . #{unparse_expr(expr.expr)}"
    when TypIntro
      "typ #{expr.var} => #{unparse_expr(expr.expr)}"
    when TypFun
      case expr.tin
      when TypFun, App
        "(#{unparse_expr(expr.tin)}) -> #{unparse_expr(expr.tout)}"
      else
        "#{unparse_expr(expr.tin)} -> #{unparse_expr(expr.tout)}"
      end
    when Lamb
      "fun #{expr.arg} => #{unparse_expr(expr.body)}"
    when App
      f = case expr.f
          when Lamb, Let, TypIntro
              "(#{unparse_expr(expr.f)})"
          else
            unparse_expr(expr.f)
          end
      arg = case expr.arg
            when App, Lamb, Let
              "(#{unparse_expr(expr.arg)})"
            else
              unparse_expr(expr.arg)
            end
      "#{f} #{arg}"
    when Match
      "match #{unparse_expr(expr.scrutinee)} with\n" +
        unparse_match_patterns(expr.patterns)
    when If
      "if #{unparse_expr(expr.cond)}\n" +
        "then #{unparse_expr(expr.then_)}\n" +
        "else #{unparse_expr(expr.else_)}"
    when Class
      expr.name
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

class Typechecker
  def typecheck(stmts, tenv)
    tenv = tenv.merge(global_tenv)
    results = stmts.map do |stmt|
      stmt, result, tenv = typecheck_stmt(stmt, tenv)
    end

    results_final = results.map {|x, _| x}
    env = results.last[1]
    [results_final, env]
  end

  def typecheck_stmt_repl(stmt, tenv)
    typecheck_stmt(stmt, tenv)
  end

  private

  def global_tenv 
    {
      puts: TypScheme.new(:a, TypFun.new(:a, NilClass)),
      debug_type: TypScheme.new(:a , TypFun.new(:a , NilClass)),
    }
  end

  def typecheck_stmt(stmt, tenv)
    fail "nil typeenv" if tenv.nil?
    
    case stmt
    in Val(name:, value:) then
      tvalue = typecheck_expr(value, tenv)
      [stmt, tvalue, tenv.merge({name => tvalue})]
    in App | Lamb | If | Number | Symbol then
      [stmt, typecheck_expr(stmt, tenv), tenv]
    else
      fail "todo typecheck_stmt #{stmt} : #{stmt.class}"
    end
  end

  def typecheck_expr(expr, tenv)
    case expr
    in TypIntro(tvar, expr) then 
      texpr = typecheck_expr(expr, tenv.merge({tvar => :type}))
      TypScheme.new(tvar, texpr)
    in (Integer | String) then
      expr.class
    in Lamb(arg:, typ:, body:) then
      check_type(typ, tenv)
      tbody = typecheck_expr(body, tenv.merge({arg => typ}))
      TypFun.new(typ, tbody)
    in Symbol => s then
      type_get(s, tenv)
    in App(f:, arg:) then
      tfun = typecheck_expr(f, tenv)
      targ = typecheck_expr(arg, tenv)
      
      if tfun.is_a? TypScheme
        arg = type_get(arg, tenv)
        tfun = tsubst(tfun.var, arg, tfun.expr)
      end

      fail "Expecting a function type, found #{tfun}" unless tfun.is_a? TypFun
      fail "Expecting '#{tfun.tin.class}' found '#{targ.class}'" unless tfun.tin == targ
      
      tfun.tout
    else
      fail "todo typecheck_expr #{expr} : #{expr.class}"
    end
  end

  def type_get(typ, tenv)
      return tenv[typ] if tenv.key? typ
      
      begin
        return Object.const_get(typ)
      rescue StandardError
        fail "unbounded type #{typ}"
      end
  end

  def tsubst(sym, value, texpr)
    case texpr
    in Symbol then
      if texpr == sym
        value
      else
        texpr
      end
    in TypFun(tin:, tout:) then
      TypFun.new(tsubst(sym, value, tin), tsubst(sym, value, tout))
    in TypApp(typ:, arg:) then
      TypApp.new(tsubst(sym, value, typ), tsubst(sym, value, arg))
    in TypScheme(var:, expr:) then
      if var == sym
        texpr
      else
        TypScheme.new(var, tsubst(sym, value, expr))
      end
    else
      const_types = [Integer, String, TrueClass, FalseClass, NilClass]
      if const_types.include?(texpr)
        return texpr
      end
      fail "todo tsubst #{texpr}"
    end
    
    
  end
  def check_type(typ, tenv)
    case typ
    when Symbol
      if tenv.key? typ
        return tenv[typ]
      end

      begin
        return Object.const_get(typ)
      rescue StandardError
        fail "unbounded type #{typ}" unless tenv.key? typ
      end
s    end
  end
end

class Interpreter
  def eval(stmts)
    eval_stmts(stmts, global_env)
  end

  def eval_stmt_repl(stmt, env)
    stmt, env = eval_stmt(stmt, env)
  end

  def global_env
    {
      puts: ->(a) { puts a; a },
      fix: method(:fix).curry,
      add: ->(a, b) { a + b }.curry,
      mul: ->(a, b) { a * b }.curry,
      sub: ->(a, b) { a - b }.curry,
      eq: ->(a, b) { a == b }.curry,
      readfile: ->(a) { File.read(a) },
      not: ->(a) { not a },
    }
  end

  private

  def fix(f, x)
    fixm = method(:fix).curry
    f.call(fixm.call(f)).call(x)
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
      [stmt.value, env]
    else
      [eval_expr(stmt, env), env]
    end
  end

  def eval_expr(expr, env)
    case expr
    when App
      if expr.f == :debug_type
        eval_expr(expr.arg, env)
      else
        f = eval_expr(expr.f, env)
        arg = eval_expr(expr.arg, env)
        case f
        when Proc, Method
          eval_expr(f.call(arg), env)
        else
          fail "bad application #{expr}"
        end
      end
    when Lamb
      ->(x) { eval_expr(expr.body, env.merge({expr.arg => x})) }
    when Symbol
      # @TODO: Deal with types like Integer
      # ex: (typ a => fun x : a => x) Integer
      if env.key? expr
        eval_expr(env[expr], env)
      end

      fail "Unbounded symbol #{expr}"
    when If
      cond = eval_expr(expr.cond, env)
      if cond
        eval_expr(expr.then_, env)
      else
        eval_expr(expr.else_, env)
      end
    when TypIntro
      eval_expr(expr.expr, env)
    when Class, Method, Proc, Integer, String, NilClass, TrueClass, FalseClass # puts return nil
      expr
    else
      fail "bad expression #{expr.class} #{expr}"
    end
  rescue StandardError => e
    puts "error with #{expr}"
    raise e
  end
end

class Runner
  def initialize
    @parser = Parser.new
    @unparser = Unparser.new
    @desuger = Desuger.new
    @typechecker = Typechecker.new
    @interpreter = Interpreter.new
  end

  def run(text)
    ast = @parser.parse(text)
    # ast = @desuger.desugar(ast)
    ast, tresults, tenv = @typechecker.typecheck(ast, {})
    puts(@unparser.unparse(ast))
    puts(@unparser.unparse([tresults]))
    # @interpreter.eval(ast)
    nil
  end
end

class REPL
  def initialize
    @parser = Parser.new
    @unparser = Unparser.new
    @desuger = Desuger.new
    @typechecker = Typechecker.new
    @interpreter = Interpreter.new
    @tenv = {}
    @ienv = @interpreter.global_env
  end

  def history_path
    @history_path ||= File.expand_path('~/.small_history')
  end

  def run
    FileUtils.touch(history_path) unless File.exist?(history_path)
    Readline::HISTORY.push(*File.readlines(history_path))
    loop do
      line = Readline.readline("> ", true)&.rstrip
      if line.nil? # Ctrl+D
        break
      elsif line.empty?
        Readline::HISTORY.pop
        next
      elsif line == Readline::HISTORY.to_a[-2]
        Readline::HISTORY.pop
      end
      break if line == "exit"
      run_stmt_text(line)
    rescue Interrupt
      break
    rescue StandardError => e
      puts "Error : #{e}"
      raise if ENV['THROW_ERROR']
    end
    File.write(history_path, Readline::HISTORY.to_a.join("\n"))
  end

  private 

  def run_stmt_text(stmt_text)
    if stmt_text == "ienv"
      pp @ienv
    elsif stmt_text == "tenv"
      pp @tenv
    else
      ast = @parser.parse(stmt_text)
      ast = @desuger.desugar(ast)
      ast.each do |stmt|
        case stmt
        when Symbol
          fail "unbounded variable #{stmt}" unless @tenv.key? stmt
          t = @tenv[stmt]
          puts "#{stmt} : #{@unparser.unparse([t])}"
        else
          stmt, t, @tenv = @typechecker.typecheck_stmt_repl(stmt, @tenv)
          value,  @ienv = @interpreter.eval_stmt_repl(stmt, @ienv)
          if [Proc, Method].include?(value.class) || stmt.is_a?(Val)
            puts "#{@unparser.unparse([stmt])} : #{@unparser.unparse([t])}"
          else 
            puts "#{@unparser.unparse([value])} : #{@unparser.unparse([t])}"
          end
        end
      end
    end
  end
end

def main
  if $stdin.tty?
    REPL.new.run
  else
    Runner.new.run($stdin.read)
  end
end

if __FILE__ == $0 # hacky for debugging in irb
  main
end
