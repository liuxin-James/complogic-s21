import algebra


namespace hidden

inductive Action_D4 : Type
| R0
| R90
| R180
| R270
| H
| V 
| D
| D'

open Action_D4
#check Action_D4

def comp: Action_D4 → Action_D4 → Action_D4
| R0 b := b
| b R0 := b
| R90 R90 := R180
| R90 R180 := R270
| R90 R270 := R0
| R90 H:= D'
| R90 V:= D
| R90 D:= H
| R90 D':= V
| R180 R90:= R270
| R180 R180:= R0
| R180 R270:= R90 
| R180 H:= V
| R180 V:= H
| R180 D:= D'
| R180 D':= D
| R270 R90:= R0
| R270 R180:= R90
| R270 R270:= R180
| R270 H:= D
| R270 V:= D'
| R270 D:= V
| R270 D':= H
| H R90:= D
| H R180:= V
| H R270:= D'
| H H:= R0
| H V:= R180
| H D:= R90
| H D':= R270
| V R90:= D'
| V R180:= H
| V R270:= D
| V H:= R180
| V V:= R0
| V D:= R270
| V D':= R90
| D R90:= V
| D R180:= D'
| D R270:= H
| D H:= R270
| D V:= R90
| D D:= R0
| D D':= R180
| D' R90:= H
| D' R180:= D
| D' R270:= V
| D' H:= R90
| D' V:= R270
| D' D:= R180
| D' D':= R0

#reduce comp R0 D

universe u

def fold {α: Type u}: α → (α → α → α) → list α → α
| a f [] := a
| a f (h::t) := f h (fold a f t)

def comp_list (a: list Action_D4): Action_D4:= fold R0 comp a

#reduce comp_list [R0,R180,R180,R90]
#reduce comp_list [R90,H]

end hidden

def band_tactic: bool → bool → bool :=
begin
assume x y,
cases x,
exact ff,
cases y,
exact ff,
exact tt,
end
#eval band_tactic tt ff
