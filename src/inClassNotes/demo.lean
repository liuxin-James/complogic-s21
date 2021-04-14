inductive sqr_pred : nat → nat → Prop
| in_sqr_pred : ∀ (n1 n2 : nat), (n2 = n1*n1) → sqr_pred n1 n2


open sqr_pred


#check sqr_pred 3 6
example : sqr_pred 3 9:= in_sqr_pred _ _ (eq.refl _)

example : sqr_pred 3 9:=
begin
  apply in_sqr_pred _ _ _,
  exact (eq.refl _),
end

theorem verification : ∀ (n1 n2 : nat), sqr_pred n1 n2 → n1 * n1 = n2 :=
begin
  assume n1 n2,
  assume h,
  cases h,
  apply eq.symm _,
  assumption,
end

#check verification

def evn : nat → bool := λ n, n%2 = 0

inductive sqr_ev_pred : nat → nat → Prop
| ev_sqr_pred : ∀ (n1 n2 : nat), (n1%2 = 0) → (n2 = n1*n1) → sqr_ev_pred n1 n2

open sqr_ev_pred

example : sqr_ev_pred 4 16 :=
begin
  apply ev_sqr_pred _ _,
  exact eq.refl 0,
  exact eq.refl 16,
end


example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  cases h,
  split,
  assumption,
  assumption,
end

example (p q : Prop) : p ∧ q → q ∧ p :=
assume ⟨h₁, h₂⟩,
and.intro (by assumption) (by assumption)


example (P Q : Prop) : P ∧ Q → Q ∧ P :=
λ (h : P ∧ Q), and.intro h.right h.left

example : ∀ (a b : nat), a = b → b = a :=
begin
introv h,
exact h.symm,
end

example : ∀ a b : nat, a = b → ∀ c, b = c → a = c :=
begin
introv h₁ h₂,
exact h₁.trans h₂,
end