import inClassNotes.typeclasses.functor
import inClassNotes.typeclasses.algebra

open alg
/-
Copy this file to where you want to work on 
it and then adjust the imports accordingly.
Work through the file following directions
as indicated. Turn in your completed file on
Collab.
-/
universe  u
universe  v
/-
1. We've imported our definitions from our
class on basic algebraic structures, such as
monoid and group. Go learn what an algebraic
*ring* is, define a typeclass that expresses
its definition, and define an instance that
expresses the claim that the integers (ℤ or
*int* in Lean) is a ring. You may "stub out"
the required proofs with *sorry*. 
-/
class distrib (α : Type u) extends has_mul α, has_add α :=
(left_distrib : ∀ a b c : α, a * (b + c) = (a * b) + (a * c))
(right_distrib : ∀ a b c : α, (a + b) * c = (a * c) + (b * c))

class ring (α : Type u) extends add_comm_group α, mul_monoid α, distrib α

#check ring

instance ring_Z: ring ℤ:= ⟨sorry, sorry⟩ 

/-
2. Go learn what an algebraic *field* is, then
define a typeclass to formalize its definition, 
and finally define two instances that express
the claims that the rational numbers (ℚ) and 
the real numbers (ℝ) are both fields. Again you
may (and should) stub out the proof fields in
your instances using sorry.
-/
class mul_comm_semigroup (α : Type u) extends mul_semigroup α :=
(mul_comm : ∀ a b : α, a * b = b * a)

class comm_ring (α : Type u) extends ring α, mul_comm_semigroup α

class field (α : Type u) extends comm_ring α, has_inv α, nontrivial α :=
(mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : α)⁻¹ = 0)

instance field_R: field ℝ:= ⟨sorry, sorry, sorry⟩ 
instance field_Q: field ℚ:= ⟨sorry, sorry, sorry⟩ 

/-
3. Graduate students required. Undergrads extra
credit. Go figure out what an algebraic module is
and write a typeclass to specify it formally. 
Create an instance to implement the typeclass for
the integers (ℤ not ℕ). Stub out the proofs. In
lieu of a formal proof, present a *brief informal*
(in English) argument to convince your instructor
that the integers really do form a module under
the usual arithmetic operators.
-/
class add_comm_semigroup (α : Type u) extends add_semigroup α :=
(add_comm : ∀ a b : α, a + b = b + a)

class add_comm_monoid (M : Type u) extends add_monoid M, add_comm_semigroup M

class semiring (α : Type u) extends add_comm_monoid α, monoid_with_zero α, distrib α

class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)

class mul_action (α : Type u) (β : Type v) [mul_monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) * b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) * b = x * y * b)


class distrib_mul_action (α : Type u) (β : Type v) [mul_monoid α] [add_monoid β] extends mul_action α β :=
(smul_add : ∀(r : α) (x y : β), r • (x + y) = r • x + r • y)
(smul_zero : ∀(r : α), r • (0 : β) = 0)

class semimodule (α : Type u) (β : Type v) [semiring α]
  [add_comm_monoid β] extends distrib_mul_action α β :=
(add_smul : ∀(r s : α) (x : β), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : β, (0 : α) • x = 0)

abbreviation module (α : Type u)(β: Type v) [ring α] [add_comm_group β] := semimodule α β

instance module_R_M: module ℤ ℤ:= ⟨sorry, sorry, sorry⟩ 

/-
4. The set of (our representations of) natural
numbers is defined inductively. Here's how they
are defined, copied straight from Lean's library.

inductive nat
| zero : nat
| succ (n : nat) : nat

Complete the following function definitions 
for natural number addition, multiplication,
and exponentiation. Write your own functions
here without using Lean's implementations 
(i.e., don't use nat.mul, *, etc). You may
not use + except as a shorthand for using 
the nat.succ constructor to add one. If you
need to do addition of something other than
one, use your own add function. Similarly, if
you need to multiply, using your mul function.
-/

def add : nat → nat → nat
| 0 m         := m
| (n' + 1) m  := (add n' m) + 1

def mul : nat → nat → nat
| 0 m         := 0
| (n' + 1) m  :=  add (mul n' m) m 

-- first arg raised to second
def exp : nat → nat → nat 
| n 0 := 1
| n (m'+1) :=  mul n (exp n m')

#eval exp 2 10    -- expect 1024

/-
5. Many computations can be expressed 
as compositions of map and fold (also 
sometimes called reduce). For example,
you can compute the length of a list
by mapping each element to the number,
1, and by the folding the list under
natural number addition. A slightly 
more interesting function counts the
number of elements in a list that 
satisfy some predicate (specified by
a boolean-returning function). 

A. Write a function, mul_map_reduce, that 
takes (1) a function, f : α → β, where β
must be a monoid; and (2) a list, l, of
objects of type α; and that then uses f
to map l to a list of objects of a type, 
β, and that then does a fold on the list 
to reduce it to a final value of type β. 

Be sure to use a typeclass instance in 
specifying the type of your function to 
ensure that the only types that can serve
as values of β have monoid structures.
Use both our mul_monoid_foldr and fmap
functions to implement your solution.
-/

open alg
#check @mul_monoid_foldr
#check @fmap

-- Your answer here
-- instance has_one_nat : alg.has_one nat := ⟨ 1 ⟩ 
-- instance mul_groupoid_nat : mul_groupoid nat := ⟨ nat.mul ⟩ 
-- instance mul_semigroup_nat : mul_semigroup nat := ⟨ _ ⟩ 
-- instance mul_monoid_nat : mul_monoid nat := ⟨ _ , _ ⟩ 

def mul_map_reduce {α β: Type} [mul_monoid β] (f: α → β) (l: list α) : β := mul_monoid_foldr (fmap f l)

#check @mul_map_reduce
/-
B. Complete the given application of 
mul_map_reduce with a lambda expression 
to compute the product of the non-zero 
values in the list 
[1,0,2,0,3,0,4].
-/

#eval mul_map_reduce  (λ n, n ≠ 0) [1,0,2,0,3,0,4]
-- expect 24

/-
6. Here you practice with type families.

A. Define a family of types, each of which
is index by two natural numbers, such that 
each type is inhabited if and only if the 
two natural numbers are equal. You may call
your type family nat_eql. Use implicit args
when it makes the use of your type family
easier. 
-/

inductive nat_eql: nat → nat → Type
| zeros_equal : nat_eql 0 0
| n_succ_m_succ_equal : Π {n m : nat}, (nat_eql n-1 m-1) → (nat_eql n m)

/-
B. Now either complete the following programs
or argue informally (and briefly) why that
won't be possible.
-/

open nat_eql

def eq_0_0 : nat_eql 0 0 := zeros_equal
def eq_0_1 : nat_eql 0 1 := _
def eq_1_1 : nat_eql 1 1 := _
def eq_2_2 : nat_eql 2 2 := _

/-
C. The apply tactic in Lean's tactic language
let's you build the term you need by applying
an already defined function. Moreover, you can
leave holes (underscores) for the arguments and
those holes then become subgoals. In this way,
using tactics allows you to build a solution 
using interactive, top-down, type-guided, aka
structured, programming! Show that eq_2_2 is
inhabited using Lean's tactic language. We get
you started. Hint: remember the "exact" tactic. 
Hint: Think *top down*. Write a single, simple
expression that provides a complete solution
*except* for the holes that remain to be filled.
Then recursively "fill the holes". Continue 
until you're done. Voila! 
-/

def eq_10_10 : nat_eql 10 10 :=
begin
end

/-
In Lean, "repeat" is a tactic that takes
another tactic as an argument (enclosed in
curly braces), applies it repeatedly until
it fails, and leaves you in the resulting 
tactic state. Use the repeat tactic to 
show that "nat_eql 500 500" is inhabited.
If you get a deterministic timeout, pick
smaller numbers, such as 100 and 100. It's
ok with us.
-/

def eq_500_500 : nat_eql 500 500 :=
begin
end


/-
7. Typeclasses and instances are used in Lean
to implement *coercions*, also known as type
casts. 

As in Java, C++, and many other languages,
coercions are automatically applied conversions
of values of one type, α, to values of another 
type, β, so that that values of type α can be
used where values of type β are needed.

For example, in many languages you may use an 
integer wherever a Boolean value is expected. 
The conversion is typically from zero to false
and from any non-zero value to true. 

Here's the has_coe (has coercion) typeclass as
defined in Lean's libraries. As you can see, a
coercion is really just a function, coe, from 
one type to another, associated with the pair 
of those two types.

class has_coe (a : Sort u) (b : Sort v) :=
(coe : a → b)

A. We provide a simple function, needs_bool, 
that takes a bool value and just returns it. 
Your job is to allow this function to be 
applied to any nat value by defining a new
coercion from nat to bool. 

First define a function, say nat_to_bool, that
converts any nat, n, to a bool, by the rule that
zero goes to false and any other nat goes to tt. 
Then define an instance of the has_coe typeclass
to enable coercions from nat to bool. You should
call it nat_to_bool_coe. When you're done the
test cases below should work.
-/

def nat_to_bool : nat → bool 
| 0 := ff
| _ := tt

instance nat_to_bool_coe : has_coe nat bool := ⟨ nat_to_bool ⟩ 

def needs_bool : bool → bool := λ b, b

-- Test cases
#eval needs_bool (1:nat)  -- expect tt
#eval needs_bool (0:nat)  -- expect ff


/-
Not only are coercions, when available, applied
automatically, but, with certain limitations, 
Lean can also chain them automatically. Define 
a second coercion called string_to_nat_coe, 
from string to nat, that will coerce any string
to its length as a nat (using the string.length
function). When you're done, you should be able
to apply the needs_bool function to any string, 
where the empty string returns ff and non-empty, 
tt. 
-/


instance string_to_nat_coe : has_coe string nat := ⟨ λ (s : string), s.length ⟩ 

-- Test cases
#eval needs_bool "Hello"  -- expect tt
#eval needs_bool ""  -- expect ff

/-
Do you see how the coercions are being chained,
aka, composed, automatically?
-/

--  Good job!