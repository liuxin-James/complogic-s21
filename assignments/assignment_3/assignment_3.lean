/-
HIGHER-ORDER FUNCTION WARMUP
-/

/-
1. Write a function, double, that takes
a natural number and returns its double.
Write it using the following recursive
definition:s
- double 0 = 0
- double (n' + 1) = double n' + 2
-/
-- ANSWER HERE
def double : ℕ → ℕ 
| 0 := 0
| (n + 1) := double n + 2

#eval double 3
#eval double 0

/-
2. Write a function, map_list_nat, that 
takes as its arguments (1) a list, l, of 
natural numbers, and (2) a function, f, 
from nat to nat, and that returns a new 
list of natural numbers constructed by 
applying f to each element of l. Make f
the first argument and l the second. The
function will work by case analysis and
recursion on l.
-/

-- ANSWER HERE
universe u
def map_list_nat {α β: Type u} : (α → β) → list α → list β
| f list.nil := list.nil
| f (h::t) := (f h) :: (map_list_nat f t)

#eval map_list_nat nat.succ [1,2,3]
/-
3. Test your map_list_nat function by
applying it to several lists, both empty
and not, passing double as the function
value. Include [], [2], and [1,2,3] in
your set of test inputs and use comments
to document the expected return values.
-/
#eval map_list_nat double [1,2,3]
#eval map_list_nat double [2]
#eval map_list_nat double []

/-
4. In Lean, repr is an "overloaded"
function. When applied to a value of a
type for which it's defined (we'll see 
later  how that happens) it returns a
string representation of the value. It
is defined for the nat type, and so 
when applied to a nat value it returns
a corresponding string. It's "toString"
for Lean. Here's an example.
-/
#eval repr 5
/-
Write a function map_list_nat_string
that takes a list of nat values and
returns a list of strings in which
each nat in the given list has been
converted to a string using repr.
-/

-- ANSWER HERE
def map_list_nat_string : list ℕ → list string
| [] := []
| (h::t) := (repr h)::(map_list_nat_string t)

#eval map_list_nat_string [1,2,3]

/-
5. Write a function, filterZeros,
that takes a list of natural numbers
and returns the same list but with any
and all zero values removed. Given
[0], for example, it should return
[]; given [1,2,0,3,4,0, 0, 5] it 
should return [1,2,3,4,5].
-/

-- ANSWER HEREh::t
def filterZeros  {α : Type u} : 
  (α → bool) → list α → list α 
| f [] := []
| f (h::t) := if (f h) 
              then h::(filterZeros f t) 
              else (filterZeros f t)

def isZero (n : nat) : bool := n ≠ 0

#eval filterZeros isZero [1,2,0,3,4,0, 0, 5] 
#eval filterZeros isZero [0]

/-
6. Write a function, isEqN, that
takes a natural number, n, and returns
a function that takes a natural number,
m, and returns true (tt) if m = n and
that returns false (ff) otherwise. Be
sure to test your function.
-/

-- ANSWER HERE
def isEqN: ℕ → (ℕ→ bool) := λ n, λ m, n=m

#eval isEqN 3 4


/-
7.
Write a function filterNs that takes
a function, pred, from nat to bool 
and a list, l, of natural numbers, and
that returns a list like l but with all
the numbers that satisfy the predicate
function removed. Test your function
using isEqN to produce a few predicate
functions (functions that for a given
argument return true or false).
-/

-- ANSWER HERE
def filterNs {α : Type u} : 
  (α → bool) → list α → list α 
| f []:=[]
| f (h::t) := if (f h) 
              then (filterNs f t)
              else h::(filterNs f t) 

#eval filterNs (isEqN 4) [1,2,4,5,6]
/-
8. Write a function, iterate, that 
takes as its arguments (1) a function, 
f, of type nat → nat, and (2) a natural
number, n, and that returns a function 
that takes an argument, (m : nat), and
that returns the result of applying f 
to m n times. For example, if n = 3, it
should return f (f (f m)). The result
of applying f zero times is just m.
Hint: use case analysis on n, and 
recursion. Test your function using 
nat.succ, your double function, and
(nat.add 4) as function arguments. 
-/

-- ANSWER HERE
def iterate: (ℕ → ℕ) → ℕ → ℕ → ℕ 
| f 0 m:= m
| f (n+1) m:= iterate f n (f m)

#eval iterate nat.succ 4 4
#eval iterate double 2 4
#eval iterate (nat.add 4) 2 4

/-
9. Write a function, list_add, that takes
a list of natural numbers and returns the
sum of all the numbers in the list.
-/

-- ANSWER HERE
def list_add: list ℕ → ℕ 
| []:=0
| (h::t) := (list_add t) +h

#eval list_add [1,3,4,5,5]

/-
10. Write a function, list_mul, that takes
a list of natural numbers and returns the
product of all the numbers in the list.
-/

-- ANSWER HERE
def list_mul: list ℕ → ℕ 
| []:=1
| (h::t) := (list_mul t) * h

#eval list_mul [1,3,4]
#eval list_mul [1]

/-
11. Write a function, list_has_zero, that
takes a list of natural numbers and returns
tt if the list contains any zero values and
that returns false otherwise. Use isEqN in
your solution. Test your solution on both
empty and non-empty lists including lists
that both have and don't have zero values.
-/

-- ANSWER HERE
def list_has_zero: list ℕ → bool
| [] := ff
| (h::t) := bor (isEqN 0 h) (list_has_zero t)

#eval list_has_zero [1,2,4,0]
#eval list_has_zero [1,2,4,5]
/-
12. Write a function, compose_nat_nat,
that takes two functions, f : ℕ → ℕ,
and g : ℕ → ℕ, and that returns a
function that takes a nat, n, and that
returns g (f n). Test your function 
using at least nat.succ and double as
argument values.
-/

-- ANSWER HERE
def compose_nat_nat: (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ
| f g a := g (f a)  

#eval compose_nat_nat nat.succ double 2


/-
13. Write a polymorphic map_box function
of type 

Π (α β : Type u), 
  (α → β) → box α → box β  
  
that takes a function, f, of type 
(α → β), and a box, b, containing a 
value of type α and that returns a 
box containing that value transformed
by the application of f.  
-/

-- ANSWER HERE
structure box (α : Type u) : Type u :=
(val : α)

def map_box {α β : Type u} (f : α → β): box α → box β :=  fun a, box.mk (f a.val)

#reduce (map_box double) (box.mk 5)

/-
14. 
Write a function, map_option, that
takes a function, f, of type α → β
and an option α and that transforms
it into an option β, where none goes
to none, and some (a : α) goes to
some b, where b is a transformed by 
f.
-/


-- ANSWER HERE
def map_option {α β : Type u} : (α → β) → option α → option β
| f option.none := option.none
| f (option.some a) :=  option.some (f a)

#reduce map_option double (option.some 3)
#reduce map_option double (option.none)

/-
15. Write three functions, default_nat,
default_bool, and default_list α, each
taking no arguments (other than a type,
argument, α, in the third case), and 
each returning a default value of the
given type: a nat, a bool, and a list.
Don't overthink this: Yes, a function
that takes no arguments is basically 
a constant. You'll need to declare a
universe variable for the list problem.
-/

-- ANSWER HERE
def default_nat:


def default_bool: 


def default_list {α: Type u}: