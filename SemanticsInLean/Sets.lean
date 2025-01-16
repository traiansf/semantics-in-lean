
def relation (α : Type u) : Type u := α → α → Prop

class Reflexive (r : relation α) where
  reflexive {a : α} : r a a

class Transitive (r : relation α) where
  transitive {a b c : α} : r a b → r b c → r a c

class Antisymmetric {α : Type u} [HasEquiv α] (r : relation α) where
  antisymmetric : forall {x y}, r x y -> r y x -> x ≈ y

class OrdRel (α : Type u) where
  ordRel : relation α

infix:50 " ≼ " => OrdRel.ordRel

class POrd (r : relation α) [He : HasEquiv α] [Reflexive r] [Transitive r] [Antisymmetric r] where

def Set (α : Type u) := α → Prop

instance : Membership α (Set α) := {
  mem := λ (a : α) (s : Set α) => s a
}

def minimum [OrdRel α] (a : α) (A : Set α) : Prop :=
  a ∈ A /\ ∀ b ∈ A, a ≼ b

instance : HasEquiv (Set α) := {
  Equiv := λ s₁ s₂ : Set α => ∀ a, a ∈ s₁ ↔ a ∈ s₂
}

def Set.pred (p : α → Prop) : Set α := p

notation "{" a "|" p "}" => Set.pred (fun a => p)

def Set.subset (s₁ s₂ : Set α) : Prop :=
  ∀ {a}, a ∈ s₁ → a ∈ s₂

instance : HasSubset (Set α) := {
  Subset := Set.subset
}

def Set.of_list (l : List α) : Set α := { a | a ∈ l}

theorem Set.equiv_elim_left (s₁ s₂ : Set α):
  s₁ ≈ s₂ → s₁ ⊆ s₂ := by
  intro Heqv x Hx
  have Heqvx := Heqv x
  revert Heqvx
  apply Iff.elim
  intro Himpl _
  apply Himpl
  trivial

theorem Set.equiv_elim_right (s₁ s₂ : Set α):
  s₁ ≈ s₂ → s₂ ⊆ s₁ := by
  intro Heqv x Hx
  have Heqvx := Heqv x
  revert Heqvx
  apply Iff.elim
  intro _ Himpl
  apply Himpl
  trivial

theorem Set.equiv_intro (s₁ s₂ : Set α):
  s₁ ⊆ s₂ → s₂ ⊆ s₁ → s₁ ≈ s₂ := by
  intros H12 H21 x
  apply Iff.intro
  · apply H12
  · apply H21

instance : OrdRel (Set α) := {
  ordRel := Set.subset
}

instance : Reflexive (Set.subset : relation (Set α)) := by
  constructor
  intro a x Hx
  trivial

instance : Transitive (Set.subset : relation (Set α)) := by
  constructor
  intro a b c Hab Hbc x Hx
  apply Hbc
  apply Hab
  trivial

instance : Antisymmetric (Set.subset : relation (Set α)) := by
  constructor
  intro a b Hab Hba
  apply Set.equiv_intro
  · trivial
  · trivial

instance : @POrd (Set α) Set.subset _ _ _ _ := by
  constructor

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

/-- `EmptyCollection α` is the typeclass which supports the notation `∅`, also written as `{}`. -/
class TopCollection (α : Type u) where
  topCollection : α

notation "⊤"     => TopCollection.topCollection

instance : TopCollection (Set α) := {
  topCollection := λ _ => True
}

theorem Set.empty_minimal (A : Set α): {} ⊆ A := by
  intro x hx
  exfalso
  apply hx

theorem Set.top_maximal (A : Set α): A ⊆ ⊤ := by
  intro _ _
  trivial

def Set.filtered_union (B : Set β) (s : β → Set α) : Set α :=
  {a | ∃ b ∈ B, a ∈ s b}

def Set.indexed_union: (β → Set α) -> Set α := Set.filtered_union ⊤

def Set.big_union (B : Set (Set α)) : Set α :=
  Set.filtered_union B id

notation "⋃" => Set.big_union

def Set.filtered_intersection (B : Set β) (s : β → Set α) : Set α :=
  {a | ∀ b ∈ B, a ∈ s b}

theorem Set.filtered_intersection_sub  (B : Set β) (s : β → Set α):
  ∀ b ∈ B, Set.filtered_intersection B s ⊆ s b := by
  intro b Hb a Ha
  apply Ha
  trivial

def Set.indexed_intersection: (β → Set α) → Set α := Set.filtered_intersection ⊤

def Set.big_inter (B : Set (Set α)) : Set α :=
  Set.filtered_intersection B id

notation "⋂" => Set.big_inter

theorem Set.empty_intersection: (⋂ ({} :  (Set (Set α)))) ≈ ⊤ := by
  intro x
  apply Iff.intro
  · intro; trivial
  · intro _
    intro b Hb
    trivial

theorem Set.big_inter_sub (B : Set (Set α)):
  ∀ b ∈ B, ⋂ B ⊆ b := by
  apply Set.filtered_intersection_sub

class Moore (A : Set (Set α)) where
  moore : ∀ B ⊆ A, ⋂ B ∈ A

theorem Moore.has_minimum (A : Set (Set α)):
  Moore A → minimum (⋂ A) A := by
  intro Hmoore
  apply And.intro
  · apply moore
    intro x Hx
    trivial
  · apply Set.big_inter_sub

structure Rule (α : Type) : Type where
  mk :: (premise : List α) (conclusion : α)

def Set.rule_closed (s : Set α) (r : Rule α) : Prop :=
  Set.of_list (r.premise) ⊆ s -> r.conclusion ∈ s

def Set.rule_set_closed (s : Set α) (R : Set (Rule α)) : Prop :=
  ∀ r ∈ R, Set.rule_closed s r

instance (R : Set (Rule α)) : Moore {s | Set.rule_set_closed s R} := by
  constructor
  intro B HB r Hr Hpr A HA
  simp
  apply (HB HA _ Hr)
  intro h Hh
  have Hh' := (Hpr Hh)
  apply (Set.big_inter_sub B A HA)
  assumption

def Set.defined_by_rule_set (R : Set (Rule α)) : Set α :=
  ⋂ {s | Set.rule_set_closed s R}

def Type.defined_by_rule_set (R : Set (Rule α)) : Type := Σ' a, a ∈ Set.defined_by_rule_set R

theorem Set.defined_by_rule_set.closed (R : Set (Rule α)) :
  Set.rule_set_closed (Set.defined_by_rule_set R) R := by
  apply (@Moore.moore _ {s | Set.rule_set_closed s R})
  intro a Ha; trivial

theorem Set.defined_by_rule_set.ind (R : Set (Rule α)) (P : α -> Prop):
  Set.rule_set_closed P R -> ∀ a ∈ Set.defined_by_rule_set R, P a := by
  intro Hc a
  change (Set.defined_by_rule_set R ⊆ P)
  clear a
  apply Set.big_inter_sub
  assumption

class UniqueReadability (R : Set (Rule α)) : Prop :=
  unique_readability :
    ∀ x ∈ Set.defined_by_rule_set R, ∀ r1 ∈ R, ∀ r2 ∈ R,
    Rule.conclusion r1 = x -> Rule.conclusion r2 = x ->
    Set.of_list (r1.premise) ⊆ (Set.defined_by_rule_set R) ->
    Set.of_list (r2.premise) ⊆ (Set.defined_by_rule_set R) ->
    r1 = r2

theorem unique_readability (R : Set (Rule α)) [UniqueReadability R] :
  ∀ x ∈ Set.defined_by_rule_set R, ∃ r ∈ R, r.conclusion = x ∧ Set.of_list (r.premise) ⊆ Set.defined_by_rule_set R := by
  apply Set.defined_by_rule_set.ind
  intro r Hr Hpr
  exists r
  constructor
  · assumption
  · constructor
    · trivial
    · intro h Hh
      have Hpr' := Hpr Hh
      obtain ⟨r', ⟨Hr', ⟨Hconc', Hpr'⟩⟩⟩ := Hpr'
      subst h
      apply Set.defined_by_rule_set.closed
      · trivial
      · trivial

def List.annotate {P : α -> Prop} (l : List α) (Hl : ∀ x ∈ l, P x) : List (Σ' a, P a) :=
  match l with
  | [] => []
  | a :: l' => ⟨a, by { apply Hl; left } ⟩ ::
    List.annotate l' (by { intro x Hx; apply Hl; right; assumption })


noncomputable def Set.defined_by_rule_set.read {R : Set (Rule α)} [UniqueReadability R]
  (x: Type.defined_by_rule_set R) : Σ' H : List (Type.defined_by_rule_set R), Rule.mk (List.map (λx => x.fst) H) (x.fst) ∈ R :=
  let l := List.annotate (Exists.choose (unique_readability R x.fst x.snd)).premise _
  ⟨l,
    by { have Heq : Rule.mk (List.map (fun x => x.fst) l) x.fst = Exists.choose (unique_readability R x.fst x.snd)





       } ⟩

def RuleSetAggregationFns (R : Set (Rule α)) (β : Type) : Type :=
  ∀ r ∈ R, List β -> β

def FnDefByRules {R : Set (Rule α)} [UniqueReadability R] (F : RuleSetAggregationFns R β) (f : Type.defined_by_rule_set R -> β) : Prop :=
  ∀ x : Type.defined_by_rule_set R,
  let r := Set.defined_by_rule_set.read x
  f x = F r.fst r.snd (map )
