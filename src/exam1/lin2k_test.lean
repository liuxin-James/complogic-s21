import data.real.basic
import exam1.lin2k


-- Let's work with rational number field
abbreviation K := ℚ  

-- Here are nice abbreviations for types
abbreviation scalr := K
abbreviation vectr := K × K

/-
1A. [10 points]

Declare v1, v2, and v3 to be of type
vectr with values (4,6), (-6,2), and
(3, -7), respectively.
-/

-- HERE
def v1: vectr := ⟨4,6⟩ 
def v2: vectr := ⟨-6,2⟩ 
def v3: vectr := ⟨3, -7⟩ 
/-
1B. [10 points]

Now define v4, *using the vector 
space operators, + and •, to be 
the following "linear combination"
of vectors: twice v1 plus negative 
v2 plus v3. The negative of a vector
is just -1 (in the field K) times
the vector. Write -1 as (-1:K), as 
otherwise Lean will treat it as the 
integer -1. (Note that subtraction
of vectors, v2 - v1 is defined as
v2 + (-1:K) • v1.)
-/
def v4: vectr := 2 • v1 + (-1:K) • v2 + v3
-- HERE 

/-
Compute the correct answer by hand
here, showing your work, and check
that eval is producing the correct
answer. 
-- HERE

-/
--(17,3)
#eval v4
/-
1C. [10 points]

On a piece of paper, draw a picture
of the preceding computation. Make a
Cartesian plane with x and y axes. 
Draw each vector, v1, v2, v3, as an
arrow from the origin to the point
designated by the coordinates of the
vector.

Scalar multiplication stretches or
shrinks a vector by a given factor.
Show each of the scaled vectors in 
your picture: 2 • v1 and (-1:K) • v2. 

Finally vector addition in graphical
terms works by putting the tail (non
arrow) end of one vector at the head
of the other then drawing the vector
from the tail of the first to the head
of the second. Draw the vectors that
illustrate the sum, 2 • v1 + (-1:K) • v2,
and then the sum of that with v3. You
should come out with the same answer
as before. Take a picture of your
drawing and upload it with your test.
-/

-- HERE

/-
2. [15 points]

Many sets can be viewed as fields. For 
example, the integers mod p, where p is
any prime, has the structure of a field
under the usual operations of addition
and multiplication mod p.

In case you forget about the integers 
mod n, it can be understood as the set
of natural numbers from 0 to n-1, where
addition and multiplication wrap around.

For example, the integers mod 5 is the
set {0, 1, 2, 3, 4}. Now 2 + 2 = 4 but
2 + 3 = 5 = 0. It's "clock arithmetic," 
as they say. Similarly 2 * 2 = 4 but 
2 * 3 = 6 = 5 + 1 = 0 + 1 = 1. 

To show informally that the integers 
mod 5 is a field you have to show that
every element of the set has an additive
inverse and that every element of the 
set but 0 has a multiplicative inverse.

Draw two tables below with the values
of the integers mod 5 in each of the 
left column. In the second column of
the first table, write in the additive
inverses of each element. In the second
table, write the multiplicative inverses.
-/

--additive inverses
| 0  | 0 |
| 1  | 4 |
| 2  | 3 | 
| 3  | 2 | 
| 4  | 1 | 
--multiplicative inverses
| 0  | _ |
| 1  | 1 |
| 2  | 3 | 
| 3  | 2 | 
| 4  | 4 | 
-- HERE

/-
4. [15 points]
Is the integers mod 4 a field? If so,
prove it informally by writing tables
giving the inverses. If not, show that
not every value in the integers mod 4
(except 0) has a multiplicative inverse,
identify a value that doesn't have an
inverse, and briefly explain why.
-/

-- HERE
Integers mod 4 is not a field, since 2 does not have a multiplicative inverse.

--multiplicative inverses
| 0  | _ |
| 1  | 1 |
| 2  | _ | 
| 3  | 3 | 

/-
5. [20 points]
Write a function, sum_vectrs, that 
takes a list of our vectr objects as 
an argument and that reduces it to a 
single vector sum. To implement your
function use a version of foldr as we
developed it: one that takes an additive
monoid implicit instance as an argument, 
ensuring consistency of the operator we
are using to reduce the list (add) and 
the corresponding identity element. 
Copy and if needed modify the foldr
definition here. It should use Lean's 
monoid class, as we've done throughout
this exercise. You do not need to and
should not try to use our algebra.lean 
file. Test your function by creating a
list of vectrs, [v1, v2, v3, v4], from
above, compute the expected sum, and
show that your function returns the 
expected/correct result.
-/
universe u
def add_monoid_foldr 
  {α : Type u} 
  [add_monoid α] 
  :
  list α → α 
| [] := has_zero.zero
| (h::t) := has_add.add h (add_monoid_foldr t)  
-- HERE

--(18,4) = (4,6) + (-6,2) + (3, -7) + (17,3)
#eval add_monoid_foldr  [v1,v2,v3,v4]

/-
6. Required for graduate students,
optional extra credit for undergrads.

The set of integers mod p can be viewed
as a field with the usual addition and
multiplication operations mod p. These 
finite fields (with only a finite number 
of elements) play a crucial role in many 
areas of number theory (in mathematics), 
and in cryptography in computer science.


A. [20 points]

Instantiate the field typeclass for
the integers mod 5 (a prime). You 
may and should stub out the proofs 
all along the way using "sorry", but
before you do that, convince yourself
that you are *justified* in doing so.

Use a "fake" representation of the
integers mod 5 for this exercise: as
an enumerated type with five values. 
Call them zero, one, two, three, and
four. Then define two functions, 
z5add and z5mul, to add and multiply
values of this type. You can figure
out the addition and multiplication
tables and just write the functions
by cases to return the right result
in each case. Start with Lean's field
typeclass, see what you need to 
instantiate it, and work backwards, 
recursively applying the same method 
until your reach clases that you can
implement directly. Put your code for
this problem below this comment.

Replace the following "assumptions" 
with your actual definitions (commenting
out the axioms as you replace them). You
can right away right click on "field" and
"go to definition" to see what you need
to do. Solving this problem will require
some digging through Lean library code.
-/
inductive Z5 : Type
| zero
| one
| two
| three
| four

-- axioms 
--   (Z5 : Type) 
--   (zero one two three four: Z5)

open Z5
-- HERE


def z5add: Z5 → Z5 → Z5 
| zero zero :=  zero
| zero one := one
| zero two := two
| zero three := three
| zero four := four
| one zero := one
| one one := two
| one two := three
| one three := four
| one four := zero
| two zero  := two
| two one  := three
| two two  := four
| two three  := zero
| two four  := one
| three zero := three
| three one := four
| three two := zero
| three three := one
| three four := two
| four zero := four
| four one := zero
| four two := one
| four three := two
| four four := three


def z5mul: Z5 → Z5 → Z5 
| zero _ := zero
| one zero := zero
| one one := one
| one two := two
| one three := three
| one four := four
| two zero  := zero
| two one  := two
| two two  := four
| two three  := one
| two four  := three
| three zero := zero
| three one := three
| three two := one
| three three := four
| three four := two
| four zero := zero
| four one := four
| four two := three
| four three := two
| four four := one

--add_comm_group
instance : has_zero Z5 := ⟨ zero ⟩ 
instance : has_add Z5 := ⟨ z5add ⟩ 
lemma add_assoc_Z5: ∀ (a b c : Z5), z5add a (z5add b c) = z5add (z5add a b) c := sorry
instance : add_semigroup Z5 := ⟨ add_assoc_Z5 ⟩ 
lemma add_ident_left : ∀ (a : Z5), z5add zero a = a := sorry
lemma add_ident_right: ∀ (a: Z5), z5add a zero = a := sorry
instance : add_monoid Z5 := ⟨ add_ident_left , add_ident_right⟩ 
lemma add_left_ident : ∀ (a : Z5), ∃ (i : Z5), z5add i a = zero := sorry
lemma add_right_ident : ∀ (a : Z5), ∃ (i : Z5), z5add a i = zero := sorry
instance : add_group Z5 := ⟨add_left_ident, add_right_ident⟩ 
lemma add_comm_Z5 : ∀ (a b : Z5), z5add a b = z5add b a := sorry
instance : add_comm_group Z5 := ⟨ add_comm_Z5 ⟩ 

--mul_comm_group
instance : has_one Z5 := ⟨ one ⟩ 
instance : has_mul Z5 := ⟨ z5mul ⟩ 
lemma mul_assoc_Z5: ∀ (a b c : Z5), z5mul a (z5mul b c) = z5mul (z5mul a b) c := sorry
instance : semigroup Z5 := ⟨ mul_assoc_Z5 ⟩ 
lemma mul_ident_left : ∀ (a : Z5), z5mul one a = a := sorry
lemma mul_ident_right: ∀ (a: Z5), z5mul a one = a := sorry
instance : monoid Z5 := ⟨ mul_ident_left , mul_ident_right⟩ 
lemma mul_left_ident : ∀ (a : Z5), ∃ (i : Z5), z5mul i a = one := sorry
lemma mul_right_ident : ∀ (a : Z5), ∃ (i : Z5), z5mul a i = one := sorry
instance : group Z5 := ⟨mul_left_ident, mul_right_ident⟩ 
lemma mul_comm_Z5 : ∀ (a b : Z5), z5mul a b =z5mul b a := sorry
instance : comm_group Z5 := ⟨ mul_comm_Z5 ⟩ 

--distrib
lemma left_distrib_Z5 : ∀ a b c : Z5, z5mul a (z5add b c) = z5add (z5mul a  b) (z5mul a  c) := sorry
lemma right_distrib_Z5 : ∀ a b c : Z5, z5mul (z5add a  b) c = z5add (z5mul a  c) (z5mul b  c)  := sorry
instance : distrib Z5 := ⟨left_distrib_Z5, right_distrib_Z5⟩ 

--ring
instance : ring Z5 := ⟨ _ ⟩ 

--comm_semigroup 
lemma mul_comm_semi_Z5 : ∀ a b : Z5, z5mul a b = z5mul b  a := sorry
instance : comm_semigroup Z5 := ⟨ mul_comm_semi_Z5 ⟩ 

--comm_ring
instance : comm_ring Z5:= ⟨ _ ⟩ 

--nontrivial
lemma exists_pair_ne_Z5 : ∃ (x y :Z5), x ≠ y :=sorry
instance : nontrivial Z5 :=⟨ exists_pair_ne_Z5 ⟩  

--field 
lemma mul_inv_cancel_Z5 : ∀ {a : Z5}, a ≠ zero → a * a⁻¹ = one := sorry
lemma inv_zero_Z5 : (zero : Z5)⁻¹ = zero := sorry
instance field_Z5: field Z5 := ⟨ mul_inv_cancel_Z5, inv_zero_Z5 ⟩ 
/-
class comm_ring (α : Type u) extends ring α, comm_semigroup α

class field (K : Type u) extends comm_ring K, div_inv_monoid K, nontrivial K :=
(mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : K)⁻¹ = 0)
-/

/-
B. [15 points]

Given that you've now presumably
established that Z5 is a field,
let z5scalr be an abbreviation for
Z5, and z5vectr for Z5 ⨯ Z5. Then
use #eval to evaluate an expression
(that you make up) involving vector 
addition and scalar multiplication
using our new z5vectr objects, i.e., 
vectors over Z5. These vectors will
look like, e.g., (one, three). Work 
out the right answer by hand and
test your code to gain confidence 
that it's working correctly.
-/

-- HERE
abbreviation z5scalr [field Z5]  := Z5
abbreviation z5vectr [field Z5] := (Z5, Z5)

#check z5vectr

def z1: z5vectr  := (one, three)
def z2: z5vectr  := (two, three)
def z3: z5vectr := two • z1 + z2
#reduce z3

/-
Take away: Instantiating a typeclass
for a given type can provide a whole
set of operations and notations that
you can use to "do algebra" with that
type. The underlying types themselves
can be very diverse. That is, we can
impose the same abstract interface on
sets of objects of different kinds, 
just as we previously imposed a group
API on the elements of the symmetry 
group, D4, of a square. Here we've now
seen that we can write vector space
algebra computations involving 2-D
vectors over both the rational and
the integers mod 5. It's in this 
sense that instantiating a typeclass
for a type provides a new "API" for
manipulating values of that type.

And while languages such as Haskell
do provide typeclasses, they don't
provide a language in which you can
declaratively express and give proofs
of the "rules" that structures have 
to follow to be valid instances. So,
welcome to Lean, a language in which
you can write mathematics and code,
with strong automated type checking
of both code and proofs. If it has to
be right (which is the case for much
crypto code), maybe write it like so!
-/