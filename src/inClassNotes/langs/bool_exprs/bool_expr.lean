/-
true, 
false, 
true && false, 
(true && false) && true
-/

inductive bool_expr : Type
| lit_expr : bool → bool_expr 
| and_expr : bool_expr → bool_expr → bool_expr 
| or_expr : bool_expr → bool_expr → bool_expr 
| not_expr : bool_expr → bool_expr 

open bool_expr 

notation e1 && e2 := and_expr e1 e2
notation e1 || e2 := or_expr e1 e2
notation ¬ e1 := not_expr e1
notation `[` b `]` := lit_expr b

def true_expr : bool_expr := [tt]
def false_expr : bool_expr := [ff]
def e3 := and_expr (lit_expr tt) [ff]
def e4 := and_expr e3 [tt]

def e3' := [tt] || [ff]
def e4' := e3' || [tt]

def e3'' := ¬  [ff]
def e4'' := ¬  [tt]



-- That's the syntax

-- Now for the semantics

def bool_eval : bool_expr → bool
| (lit_expr b) := b
| (and_expr e1 e2) := band (bool_eval e1) (bool_eval e2)
| (or_expr e1 e2) := bor (bool_eval e1) (bool_eval e2)
| (not_expr e1) := bnot (bool_eval e1)


#eval bool_eval e4
#eval bool_eval e4'
#eval bool_eval e4''
#eval bool_eval e3''


-- assert and prove the proposition that for *any* Boolean expressions, e1 and e2, in LLBE, e1 && e2 "means" the same thing as e2 && e1

example : ∀ (e1 e2: bool_expr), bool_eval (e1 && e2) = bool_eval (e2 && e1) :=
begin
  assume a b,
  cases a1 : bool_eval a,
  cases b1: bool_eval b,
  apply bool_eval (a && b),
  exact bool_eval (b && a),
end