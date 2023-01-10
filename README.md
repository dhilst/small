# small

_small_ is a ML language, like SML and OCaml featuring Algebraic Data Types
encoded as functions using Scott Encoding, and HM type system.

_small_ because it's a small ML and the pronunciation is close to SML

# Basic structure

Programs in _small_ are a sequence of statements separated by `;`, please
note that a leading `;` is considered a syntax error. Statements in turn may
contain expressions, there are two statements for now, `val` and `data`, more
about this next. You can also use `#` to start line comments, comments
are removed during the lexing phase.

# The core language

The core language is composed of anonymous function definition,
function application, if/else expressions, and global defintions.

Being the core language means that all other languages constructs are syntax
sugar for these constructs

## Anonymous function definition

You can define a function using the following syntax:

```sml
fun x => x
```

All functions have a single argument and return a single expression, you
can declare multiple argument functions with currying, example:

```sml
fun x => fun y => x
```

## Function application

You can apply functions by placing them to the left of its arguments, example:

```sml
(fun x => x) 1
```

## If/else

If/else has the same syntax as in OCaml, the conditional, example:

```sml
if true then false else true
```

## Global values

You can bind a name to any value by using the `val` statement, example:

```sml
val id = fun x => x
```

## Non-core language

All constructions that are not in the core language compiles
down to the core language, since the most meaningful features
of the core language are function definition and function
application almost everything compiles to functions.

## Algebraic Data Types

You can define Algebraic Data Types using the `data` statement,
example:

```sml
data option = some x | none
```

This is sugar for the following:

```sml
val some =
  fun x => fun some => fun none => some x;
val none =
  fun some => fun none => none
```

## Match expressions

Match expressions are sugar for function application, example:

```sml
match x with
| some y => y
| none => 0
end
```

is sugar for

```sml
x (fun y => y) 0
```

## Let expressions

Let expressions are sugar also function application, example:

```sml
let x = 1 in x
```

Is sugar to:

```sml
(fun x => x) 1
```

# HM Type System

If you don't know what is a Hidley-Milner typesytem I recomend
the [wikipedia](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system) page.

You cannot express types in _small_, yet all the types are
infered. The type inference runs over the core language,
after the desugaring the source code. Examples:

_types are shown as comments after `:`_ 

```sml
fun x => x # : a -> a
fun x => fun y => x # : a -> b -> a
```

`... -> ...` are function types, `a b c ... z` are type variables and.

When you use a variable in a place that requires a specific type the
variable will be infered to have that type, and further uses of it
will need to be consistent with the infered type. Beside type
variables there are also primitive types, these are:

* `int` : The type for integers, they are represented internaly as
`Integer` instances in Ruby
* `bool` : Type for booleans, they are represented by `TrueClass`
or `FalseClass` instances in ruby
* `nil` : This is a special type that should behave as the inhabited
type. There are no constructors for it but some special functions
may return it (like `puts`). I plan to add a static checking to ensure
that `nil` is never used as input of any function.

Here is an example of type inference: `add` is a built-in function
with the type `int -> int -> int`, (if you are not familiar with ML
function types, this means that it receives two integers and return
another integer). If I use a variable in a position where an `int`
is expected, the type of the variable is infered to `int` and all
uses of that variable will need to be of type `int` too, example:

```sml
# because x is used as `add` input, its type
# is infered to int, so the function type is
# infered to `int -> int`
fun x => add x 1 # : int -> int
```

Now `not` is a function with the type `bool -> bool` function, here is
a example of type error

```sml
fun x =>
  let _ = add x 1 in # x now has type int
  not x # int used where a is expected, type error
```

## Universal quantification / Let polymorphism

Type inference is good but in some cases it can be too restrictive,
example:

```sml
data option = some x | none;
data pair = pair a b;

pair (some 1) (some true)
```

In this case the type inference (as explained before) would reject
this program, because `some` is desugared to a function and then used
with `int` and `bool` as its input. In this case we *want* it to infer
its type at each application, to do this we use let polymorphism
(which I call universal quantification from here on). Universal
quantification only takes place at `val` statements, functions binded
to a `val` value are universally quantified, this is denoted in their
types by the `forall` word, example:

```sml
val id = fun x => x # : forall a . a -> a
```

Please note that in traditional HM type systems the let polymorphism
is applied in `let` expressions (this is why its called let polymorphism).
This is not the case here, `let` expressions has exactly the same
semantics that function application, in fact at typechecking time the
`let` expressions were already desugared to function application.

## Unification

As you cannot express types in the grammar of the language, because of 
this you cannot easily define a function with the type `a -> a -> a`.

```sml
fun x => fun y => x # : a -> b -> a
fun x => fun y => y # : a -> b -> b
```

To remedy this there is a built-in function `unify : a -> a -> a`
which returns its second argument and you can use it to
express that two variables should have the same type.

```sml
fun x => fun y => unify y x # : a -> a -> a
fun y => fun x => unify y x # : a -> a -> a
```

This is unsound as now you can have a function that accepts a
`nil`. The built-in function `puts` has the type `forall a . a -> nil`
. It will print to the standard output whatever you pass to it.

```sml
puts (add 1 2) # outputs 3 in the standard output
```

With `puts` and `unify` you can declare a function that receives null,
which I think is not a good idea and should be fixed in future. I
didn't had any problems with `nil`, yet, but it's more a implementation
detail leaking and should be removed or restricted in future.

```sml
fun x => unify x (puts x) # nil -> nil
```

## Recursion

Recursion brings unsoundness to the language. If you are using the
language as a proof system then you can use recursion to prove anything.
Because of this (and because small intends to be as sound as possible)
recursion have to be explicitly enabled with `ENABLE_FIXPOINT` environment
variable.

Setting this environment variable to anything enables the `fix` function
which is the fixpoint combinator, with which you can express recursion,
example:

```sml
# returns the sum `x + (x - 1) + (x - 2) ... 0`
val sumfix = fum sum => fun x =>
  if eq x 0
  then 0
  else add x (sum (sub x 1));
  
puts (fix sumfix 3) # outputs 6
```

You can use recursion to do a program that would never terminates, in
practice the program terminates with a `stack level too deep` error
from the Ruby interpreter. This is why recursion is disabled by
default

```sml
val f => fun f => fun x => f x;

fix f 1
```
  
The fix combinator works by passing the function to it self. If
you try to do this without fix you get a type error, so, by default,
well-typed programs are garanteed to terminate.

```sml
val f = fun x => f x # error : unbounded variable f
val g => fun g => fun x => g g x # type error unification
                                 # error b occurs in b -> d
```

This also means that we have no recursive types

# Builtin-functions and primitives

## Types

* `int` : The type for integers, can't be matched with `match i with ...`
* `bool` : The type for bools, can't be matched with `match b with ...`
  but you can use `if b then ... else ...` if fact `if` was added only
  to destruct boolean values, I would like to remove it in future and
  add the `data bool = true | false` in future which can be matched,
  then I can remove `if` from the language. I added because it was
  so mutch easier to implement the comparsion functions using ruby
  builtins in this way.
* `nil` : Has no constructors, it is the return type of some built-in
  functions as `puts`
* `a -> b` : A function type receive `a` type  and returning `b` type
* `forall a . a -> b` : An universaly quantified function, receiving
  any `a` and returning a fixed `b` (see [Universal quantification /
  Let polymorphism](#Universal-quantification-/-Let-polymorphism)
  
## Functions

* `add : int -> int -> int` add two numbers
* `sub : int -> int -> int` subtract two numbers
* `mul : int -> int -> int` subtract two numbers
* `eq : a -> a -> bool` compare two values and return `true` if they
  are equal. Since this compiles down to `Object.==` call in ruby it
  is only reliable to use with `int` and `bool` for now
* `not : bool -> bool` returns the negation of its input
* `unify : a -> a -> a` returns its second argument and can be used to
  restrict two variables to the same type
* `puts : a -> nil` the `puts` function from ruby, mainly for debug

# Running

Use `rake` to build the `parser.rb` file, then `ruby rml.rb`

```shell
rake
ruby small.rb
```

This will run the REPL where you can type statements

# TODO

* Parse/Run files (when stdin is not tty)

