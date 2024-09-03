import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation
import Mathlib.Logic.Relation

inductive AExp where
  | num (n : ℤ) : AExp
  | var (l : ℕ) : AExp
  | plus (a1 a2 : AExp) : AExp
  | minus (a1 a2 : AExp) : AExp
  | mul (a1 a2 : AExp) : AExp

inductive BExp where
  | bool (b : Bool) : BExp
  | eq (a1 a2 : AExp) : BExp
  | le (a1 a2 : AExp) : BExp
  | not (b : BExp) : BExp
  | and (b1 b2 : BExp) : BExp
  | or (b1 b2 : BExp) : BExp

inductive Stmt where
  | skip : Stmt
  | asgn (l : ℕ) (a : AExp) : Stmt
  | seq (s1 s2 : Stmt) : Stmt
  | ite (b : BExp) (s1 s2 : Stmt) : Stmt
  | while (b : BExp) (s : Stmt) : Stmt

def State : Type := ℕ → ℤ

instance : Inhabited State where
  default := λ _ => 0

def State.get (s : State) (n : ℕ) : ℤ := s n

def State.update (s : State) (n : ℕ) (z : ℤ) : State :=
  λ x => if x = n then z else s x

def AExp.eval (a: AExp) (s : State) : ℤ :=
  match a with
  | num n => n
  | var x => s.get x
  | plus a1 a2 => a1.eval s + a2.eval s
  | minus a1 a2 => a1.eval s - a2.eval s
  | mul a1 a2 => a1.eval s * a2.eval s

def BExp.eval (b: BExp) (s : State) : Bool :=
  match b with
  | bool t => t
  | eq a1 a2 => a1.eval s = a2.eval s
  | le a1 a2 => a1.eval s <= a2.eval s
  | not b => ¬ b.eval s
  | and b1 b2 => b1.eval s ∧ b2.eval s
  | or b1 b2 => b1.eval s ∨ b2.eval s

inductive Stmt.bigStep : Stmt -> State -> State -> Prop :=
  | bsSkip : bigStep skip σ σ
  | bsAsgn : bigStep (Stmt.asgn x a) σ (σ.update x (a.eval σ))
  | bsSeq : bigStep s1 σ σ₁ -> bigStep s2 σ₁ σ₂ -> bigStep (Stmt.seq s1 s2) σ σ₂
  | bsIteTrue : b.eval σ = true -> bigStep st σ σ' -> bigStep (Stmt.ite b st _) σ σ'
  | bsIteFalse : b.eval σ = false -> bigStep se σ σ' -> bigStep (Stmt.ite b _ se) σ σ'
  | bsWhileExit : b.eval σ = false -> bigStep (Stmt.while b _) σ σ
  | bsWhileEnter : b.eval σ = true -> bigStep s σ σ' -> bigStep (Stmt.while b s) σ' σ''  -> bigStep (Stmt.while b s) σ σ''


def Stmt.omega : Stmt := Stmt.while (BExp.bool true) Stmt.skip

theorem Stmt.omega_does_not_eval :
  ¬ ∃ (σ₁ σ₂ : State), Stmt.omega.bigStep σ₁ σ₂ := by
  apply not_exists_of_forall_not; intros σ₁
  apply not_exists_of_forall_not; intros σ₂
  intros Hcontra
  generalize hc : omega = c
  rw [hc] at Hcontra
  induction Hcontra
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · cases hc
    · trivial
  · cases hc
    · trivial

def Stmt.equiv (s₁ s₂ : Stmt) : Prop :=
  ∀ σ σ': State, s₁.bigStep σ σ' ↔ s₂.bigStep σ σ'

theorem Stmt.while_unroll :
  (Stmt.while b s).equiv (Stmt.ite b (Stmt.seq s (Stmt.while b s)) Stmt.skip) := by
  intro σ σ'
  constructor
  . intro Hw
    cases Hw
    · apply bigStep.bsIteFalse
      · trivial
      · apply bigStep.bsSkip
    · apply bigStep.bsIteTrue
      · trivial
      · apply bigStep.bsSeq
        · trivial
        · trivial
  · intro Hif
    cases Hif with
    | bsIteTrue Hb Hseq =>
      cases Hseq with
      | bsSeq Hs Hw =>
        apply bigStep.bsWhileEnter
        · trivial
        · trivial
        · trivial
    | bsIteFalse Hb Hskip =>
      cases Hskip with
      | bsSkip =>
        apply bigStep.bsWhileExit
        trivial

def Config: Type := Stmt × State

inductive Config.smallStep : Config -> Config -> Prop :=
  | ssAsgn : smallStep ⟨ Stmt.asgn x a, σ ⟩ ⟨ Stmt.skip, σ.update x (a.eval σ) ⟩
  | ssSkip : smallStep ⟨ Stmt.seq Stmt.skip s, σ ⟩ ⟨ s, σ ⟩
  | ssSeq : smallStep ⟨ s₁, σ ⟩ ⟨ s₁', σ' ⟩ →
            smallStep ⟨ Stmt.seq s₁ s₂, σ ⟩ ⟨ Stmt.seq s₁' s₂, σ' ⟩
  | ssIteTrue : b.eval σ = true ->
                smallStep ⟨ Stmt.ite b s₁ s₂, σ ⟩ ⟨ s₁, σ ⟩
  | ssIteFalse :  b.eval σ = false ->
                  smallStep ⟨ Stmt.ite b s₁ s₂, σ ⟩ ⟨ s₂, σ ⟩
  | ssWhile : smallStep ⟨ Stmt.while b s, σ ⟩ ⟨ Stmt.ite b (Stmt.seq s (Stmt.while b s)) Stmt.skip, σ ⟩

def Config.smallSteps := Relation.ReflTransGen Config.smallStep

theorem smallStep_seq :
  Config.smallSteps ⟨ s₁, σ ⟩ ⟨ s₁', σ' ⟩ →
  Config.smallSteps ⟨ Stmt.seq s₁ s₂, σ ⟩ ⟨ Stmt.seq s₁' s₂, σ' ⟩ := by
  unfold Config.smallSteps
  generalize Hcfg : (s₁, σ) = cfg
  generalize Hcfg' : (s₁', σ') = cfg'
  intro Hs
  revert Hcfg Hcfg' s₁ s₁' σ σ'
  induction Hs with
  | refl =>
    intro s₁ σ s₁' σ' Hcfg Hcfg'
    subst cfg
    cases Hcfg'
    constructor
  | @tail _ _cfg' _ _ IH =>
    intro s₁ σ s₁' σ' Hcfg Hcfg'
    subst cfg _cfg'
    constructor
    · apply IH
      · trivial
      · trivial
    · constructor
      trivial

theorem smallStep_seq_to_skip :
  Config.smallSteps ⟨ s₁, σ ⟩ ⟨ Stmt.skip, σ₁ ⟩ →
  Config.smallSteps ⟨ s₂, σ₁ ⟩ ⟨ Stmt.skip, σ₂ ⟩ →
  Config.smallSteps ⟨ s₁.seq s₂, σ ⟩ ⟨ Stmt.skip, σ₂ ⟩ := by
  intros Hs1 Hs2
  apply Relation.ReflTransGen.trans
  · apply smallStep_seq
    trivial
  · apply Relation.ReflTransGen.trans
    · apply Relation.ReflTransGen.single
      constructor
    · trivial

theorem smallStep_skip_seq :
  Config.smallSteps ⟨ Stmt.skip.seq s₂, σ ⟩ cfg ->
  cfg = ⟨ Stmt.skip.seq s₂, σ ⟩ ∨
  Config.smallSteps ⟨ s₂, σ ⟩ cfg := by
  intro Hss
  have Hss_cases := (Relation.ReflTransGen.cases_head_iff.1 Hss)
  cases Hss_cases with
  | inl Heq =>
    left
    symm
    trivial
  | inr Hex =>
    cases Hex with | _ cfg Hcfg =>
      cases Hcfg with
      | _ Hseq Hskip =>
        cases Hseq with
        | @ssSeq Htail Hseq s' σ' Hσ' Hs =>
          cases Hs
        | ssSkip =>
          right
          trivial

theorem smallStep_seq_assoc :
  ∀ s₁ : Stmt,
  Config.smallSteps ⟨ (s₁.seq s₂).seq s₃, σ ⟩ cfg ->
  Config.smallSteps ⟨ s₁.seq (s₂.seq s₃), σ ⟩ cfg := by
 sorry

theorem smallStep_seq_to_skip_inv :
  Config.smallSteps ⟨ s₁.seq s₂, σ ⟩ ⟨ Stmt.skip, σ₂ ⟩ ->
  ∃ σ₁,
    Config.smallSteps ⟨ s₁, σ ⟩ ⟨ Stmt.skip, σ₁ ⟩ ∧
    Config.smallSteps ⟨ s₂, σ₁ ⟩ ⟨ Stmt.skip, σ₂ ⟩ := by
  revert s₂ σ σ₂
  induction s₁ with
  | skip =>
    intro σ σ₂ s₂ Hss
    have Hss_cases := smallStep_skip_seq Hss
    clear Hss
    cases Hss_cases with
    | inl Hcontra =>
      cases Hcontra
    | inr Hss =>
      exists σ
      constructor
      · constructor
      · trivial
  | asgn x a =>
    intro σ σ₂ s₂ Hss
    exists (σ.update x (a.eval σ))
    constructor
    · apply Relation.ReflTransGen.single
      constructor
    · have Hss_cases := (Relation.ReflTransGen.cases_head_iff.1 Hss)
      clear Hss
      cases Hss_cases with
      | inl Hcontra =>
        cases Hcontra
      | inr Hex =>
        cases Hex with | _ cfg Hcfg =>
          cases Hcfg with
          | _ Hseq Hskip =>
            cases Hseq with
            | @ssSeq Htail Hseq s' σ' Hσ' Hs =>
              cases Hs
              have Hskip_cases := smallStep_skip_seq Hskip
              cases Hskip_cases with
              | inl Hcontra =>
                cases Hcontra
              | inr Hss =>
                trivial
  | seq s₁ s₁' IHs₁ IHs₁' =>
    intro σ σ₂ s₂ Hss
    sorry
  | ite b s₁ s₂ IHs₁ IHs₂ =>
    intro σ σ₂ s Hs
    sorry
  | _ b s IHs =>
    intro σ σ₂ s₂ Hs₂
    sorry

theorem smallStep_skip_to :
  Config.smallSteps ⟨ Stmt.skip, σ ⟩ ⟨ s', σ' ⟩ -> s' = Stmt.skip ∧ σ' = σ := by
  unfold Config.smallSteps
  generalize Hcfg : (Stmt.skip, σ) = cfg
  generalize Hcfg' : (s', σ') = cfg'
  intro Hss
  revert Hcfg Hcfg' s' σ σ'
  induction Hss with
  | refl =>
    intro σ s' σ' Hcfg Hcfg'
    subst cfg
    cases Hcfg'
    trivial
  | @tail _cfg _cfg'  Hinit Htail IHinit =>
    intro σ s' σ' Hcfg _
    cases H: _cfg with
    | _ fst snd =>
      have IHinit := IHinit Hcfg (symm H)
      cases IHinit
      subst fst snd _cfg
      cases Htail

theorem smallStep_asgn_to_skip :
  Config.smallSteps ⟨ Stmt.asgn x a, σ ⟩ ⟨ Stmt.skip, σ' ⟩ -> σ' = σ.update x (a.eval σ) := by
  intro Hss
  have Hss_cases := (Relation.ReflTransGen.cases_head_iff.1 Hss)
  clear Hss
  cases Hss_cases with
  | inl Hcontra =>
    cases Hcontra
  | inr Hex =>
    cases Hex with | _ cfg Hcfg =>
      cases Hcfg with
      | _ Hasgn Hskip =>
        cases Hasgn
        have Hss := (smallStep_skip_to Hskip).2
        trivial

theorem bigStep_iff_smallStep :
  s.bigStep σ σ' ↔ Config.smallSteps ⟨ s, σ ⟩ ⟨ Stmt.skip, σ' ⟩ := by
  constructor
  · intro Hbs
    induction Hbs with
    | bsSkip =>
      constructor
    | bsAsgn =>
      apply Relation.ReflTransGen.single
      constructor
    | bsSeq Hs1 Hs2 IHs1 IHs2 =>
      apply smallStep_seq_to_skip
      · trivial
      · trivial
    | bsIteTrue Hb Hst IHst =>
      apply Relation.ReflTransGen.trans
      · apply Relation.ReflTransGen.single
        apply Config.smallStep.ssIteTrue
        trivial
      . trivial
    | bsIteFalse Hb Hst IHst =>
      apply Relation.ReflTransGen.trans
      · apply Relation.ReflTransGen.single
        apply Config.smallStep.ssIteFalse
        trivial
      . trivial
    | bsWhileEnter Hb Hst Hw IHst IHw =>
      apply Relation.ReflTransGen.trans
      · apply Relation.ReflTransGen.single
        apply Config.smallStep.ssWhile
      · apply Relation.ReflTransGen.trans
        · apply Relation.ReflTransGen.single
          apply Config.smallStep.ssIteTrue
          trivial
        · apply smallStep_seq_to_skip
          · trivial
          · trivial
    | bsWhileExit Hb =>
      apply Relation.ReflTransGen.trans
      · apply Relation.ReflTransGen.single
        apply Config.smallStep.ssWhile
      · apply Relation.ReflTransGen.trans
        · apply Relation.ReflTransGen.single
          apply Config.smallStep.ssIteFalse
          trivial
        · constructor
  · induction s with
    | skip =>
      intro Hss
      have Hskip := smallStep_skip_to Hss
      cases Hskip
      subst σ'
      constructor
    | asgn x a =>
      intro Hasgn
      have Hσ' := smallStep_asgn_to_skip Hasgn
      subst σ'
      constructor
    | @seq s₁ s₂ IHs₁ IHs₂ =>
      sorry
    | ite b s₁ s₂ IHs₁ IHs₂ =>
      intro Hss
      sorry
    | _ b s IHs =>
      intro Hss
      sorry



