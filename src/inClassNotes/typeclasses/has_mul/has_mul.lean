namespace hidden

universe u

structure has_mul_ident (α : Type u): Type (u+1) := 
(mul : α → α → α)


def has_mul_ident_type: has_mul_ident bool := has_mul_ident.mk band
#check has_mul_ident_type 
/-
Syntactic alternative:
class has_mul (α : Type u) := (mul : α → α → α)
-/
@[class]
structure has_mul (α : Type u): Type (u+1) := 
(mul : α → α → α)

instance has_mul_bool : has_mul bool := has_mul.mk band
instance has_mul_nat : has_mul nat := has_mul.mk nat.mul

def fancy_mul {α : Type} [tc: has_mul α] : α → α → α:= tc.mul

#eval fancy_mul tt ff

#eval fancy_mul 3 4


end hidden