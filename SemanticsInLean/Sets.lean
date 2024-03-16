
def Set (α : Type u) := α → Prop

instance : Membership α (Set α) := {
  mem := λ (a : α) (s : Set α) => s a
}

instance : HasEquiv (Set α) := {
  Equiv := λ s₁ s₂ : Set α => ∀ {a}, a ∈ s₁ ↔ a ∈ s₂
}

def Set.pred (p : α → Prop) : Set α := p

notation "{" a "|" p "}" => Set.pred (fun a => p)

instance : HasSubset (Set α) := {
  Subset := λ s₁ s₂ : Set α => ∀ {a}, a ∈ s₁ → a ∈ s₂
}

instance : Union (Set α) := {
  union := λ s₁ s₂ : Set α => { a | a ∈ s₁ ∨ a ∈ s₂ }
}

instance : Inter (Set α) := {
  inter := λ s₁ s₂ : Set α => { a | a ∈ s₁ ∧ a ∈ s₂ }
}

instance : SDiff (Set α) := {
  sdiff := λ s₁ s₂ : Set α => { a | a ∈ s₁ ∧ a ∉ s₂}
}

instance (s : Set α) [h : Decidable (s a)] : Decidable (a ∈ Set.pred s) :=
  h

instance (s₁ s₂ : Set α) [Decidable (a ∈ s₁)] [Decidable (a ∈ s₂)] : Decidable (a ∈ s₁ ∩ s₂) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (s₁ s₂ : Set α) [Decidable (a ∈ s₁)] [Decidable (a ∈ s₂)] : Decidable (a ∈ s₁ ∪ s₂) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance : EmptyCollection (Set α) := {
  emptyCollection := (λ _ => False)
}

theorem Set.empty_minimal (A : Set α): {} ⊆ A := by
  intro x hx
  exfalso
  apply hx
