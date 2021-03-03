def list_map {α β : Type} : (α → β) → (list α) → list β 
| f list.nil := list.nil
| f (h::t) := (f h)::(list_map f t)

#eval list_map nat.succ [1,2,3,4,5,6]