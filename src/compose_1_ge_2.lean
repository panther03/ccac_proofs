import src.trace

import Mathlib.Order.Defs.LinearOrder

namespace Compose1Ge2

structure InfB where
  -- The queue size itself
  B: ℚ
  -- Queue size is positive
  pos_B: B > 0
  -- And causes no loss
  noloss: ∀ (inp los wst: ℕ → ℚ) (C: ℚ) (t: ℕ), inp t - los t ≤ C * ↑t - (wst t) + B

@[simp]
def t_D: ℕ := 3

lemma noloss_cond_los: ∀ (IB: InfB) (wst inp: ℕ → ℚ) (C: ℚ) (t: ℕ), 0 < 0 -> (inp (1 + t) - 0) > C * ↑t - (wst t) + IB.B := by
  intros IB wst inp C t contr
  linarith [contr]

def flat : ℕ → ℚ := fun _: ℕ => 0

lemma flat_monotonic: Monotone flat := by
  unfold Monotone flat
  intros
  simp

@[simp]
def t1_C: ℚ := 2

@[simp]
def t1_wst (C1: ℚ): ℕ -> ℚ
  | 0 => 0
  | _ => C1

@[simp]
def t1_line (C1: ℚ) (t: ℕ) := (↑t * C1) - (t1_wst C1 t)

lemma t1_wst_monotonic: Monotone (t1_wst t1_C) := by
  unfold Monotone t1_C
  intros x1 x2
  induction x2 <;> intros Hx1
  . cases x1 <;> linarith
  . rename_i x2 IH
    cases Hx1
    . rfl
    . rename_i H
      specialize IH H
      calc
        _ ≤ t1_wst 2 x2 := IH
        _ ≤ _ := by (unfold t1_wst; cases x2 <;> simp)

lemma t1_line_monotonic: Monotone (t1_line t1_C) := by
  unfold Monotone t1_C
  intros x1 x2
  induction x2 <;> intros Hx1
  . cases x1 <;> linarith
  . rename_i x2 IH
    cases Hx1
    . rfl
    . rename_i H
      specialize IH H
      calc
        _ ≤ t1_line 2 x2 := IH
        _ ≤ _ := by {
          unfold t1_line t1_wst
          cases x2 <;> simp
        }

lemma t1_constraint_u: ∀ t: ℕ, (t1_line t1_C) t ≤ (t1_C) * ↑t - (t1_wst t1_C) t := by
  unfold t1_line t1_wst t1_C
  intros
  simp
  rw [mul_comm]

lemma t1_constraint_l: ∀ t: ℕ, (t1_line t1_C) t ≥ (t1_C) * ↑(t - t_D) - (t1_wst t1_C) (t - t_D) := by
  intros t
  unfold t1_C t_D
  cases' (le_or_gt t 3) with tle tgt
  . unfold t1_line t1_wst
    rw [<- Nat.sub_eq_zero_iff_le] at tle
    rw [tle]
    cases t <;> simp
  . have h: (2 * ↑(t - 3) - t1_wst 2 (t - 3) = (t1_line 2 (t-3))) := by
      unfold t1_line; simp; apply mul_comm
    rw [h]
    apply t1_line_monotonic
    rw [@Nat.sub_le_iff_le_add]
    linarith

lemma t1_cond_waste: ∀ t: ℕ, (t1_wst t1_C) t < (t1_wst t1_C) (t + 1) -> t1_line t1_C (1 + t) - 0 <= t1_C * ↑(1 + t) - (t1_wst t1_C) (1 + t) := by
  unfold t1_line t1_wst
  intros t
  cases t <;> simp

@[simp]
def mkt1 (IB: InfB): Trace := by
  refine Trace.mk t1_C IB.B t_D
    (t1_line t1_C) (t1_line t1_C) (t1_wst t1_C) (λ t: ℕ => 0)
    (?_) (?_)
    IB.pos_B t1_constraint_u t1_constraint_l t1_cond_waste (?_) (?_) (?_) t1_line_monotonic t1_line_monotonic t1_wst_monotonic flat_monotonic (?_) (?_) (?_) (?_) <;> try simp [-t_D, -t1_C, -t1_wst, -t1_line]
  . unfold t1_C; simp
  . apply IB.noloss
  . unfold t1_line t1_wst; simp
  . unfold t1_line t1_wst; simp
  . simp


@[simp]
def t2_C: ℚ := 1

@[simp]
def t2_out (C1 : ℚ) (C2: ℚ) (t: ℕ): ℚ :=
  if (t ≤ 2) then t1_line C1 t else C2 * ↑t


lemma t2_constraint_u: ∀ t: ℕ, (t2_out t1_C t2_C) t ≤ (t2_C) * ↑t - 0 := by
  unfold t2_out t1_line t1_wst t1_C t2_C
  intros t
  cases t <;> simp
  rename_i t
  split
  . rename_i h
    have h' : ↑t ≤ (1: ℚ) := by
      rw [@Nat.cast_le_one]; assumption
    linarith
  . rename_i h
    rw [Nat.not_le] at h

lemma t2_constraint_l: ∀ t: ℕ, (t2_out t1_C t2_C) t ≥ (t2_C) * ↑(t - t_D) - 0 := by
  unfold t2_out t1_line t1_wst t1_C t2_C t_D
  intros t
  cases t <;> simp
  rename_i t
  split
  . rename_i h
    have h' : t ≤ 2 := by linarith
    rw [<- Nat.sub_eq_zero_iff_le] at h'
    rw [h']
    cases t <;> simp
    linarith
  . rename_i h
    rw [Nat.not_le] at h
    rw [nat_real_sub t 2 h]
    linarith

lemma t2_out_le_inp: ∀ t: ℕ, (t2_out t1_C t2_C) t ≤ (t1_line t1_C) t := by
  intros t
  unfold t2_out t1_line
  split
  . rename_i h
    simp
  . rename_i h
    rw [Nat.not_le] at h
    unfold t2_C t1_C t1_wst
    have h' : (2: ℚ) < ↑t  := by
      rw [@Nat.ofNat_lt_cast]; assumption
    cases t <;> simp
    rename_i t
    rw [nat_real_add] at h'
    simp at h'
    linarith

lemma t2_out_step_monotone: ∀ t: ℕ, (t2_out t1_C t2_C) t ≤ (t2_out t1_C t2_C) (t + 1) := by
  intros t
  unfold t1_C t2_C t2_out t1_line t1_wst
  rcases t with _ | (_ | (_ | t)) <;> simp
  linarith

lemma t2_out_monotonic: Monotone (t2_out t1_C t2_C) := monotone_nat_of_le_succ t2_out_step_monotone

@[simp]
def mkt2 (IB: InfB): Trace := by
  refine Trace.mk t2_C IB.B t_D
    (t2_out t1_C t2_C) (t1_line t1_C) (λ t: ℕ => 0) (λ t: ℕ => 0)
    (?_) (?_)
    IB.pos_B t2_constraint_u t2_constraint_l (?_) (?_) (?_) (?_) t2_out_monotonic t1_line_monotonic flat_monotonic flat_monotonic (?_) (?_) (?_) (?_) <;> try simp [-t2_C, -t2_out]
  . unfold t2_C; simp
  . have h := IB.noloss (t1_line t1_C) (λ t: ℕ => 0) (λ t: ℕ => 0) t2_C
    simp [-t2_C] at h
    apply h
  . apply t2_out_le_inp
  . unfold t2_out t1_line t1_wst; simp



inductive WstState
  | Tracking
  | NoWst

-- Helper function. If (τₛ.w (t+1)) = this value, then τₛ.upper = τ₁.upper

def track_paper (τ₁ τ₂ : Trace) (wst_cur : ℚ) (t : ℕ) : ℚ :=
  let wst := τ₁.wst (t+1) - (τ₁.C - τ₂.C) * ↑t
    if wst_cur > wst then wst_cur else wst

def track_ours (τ₁ τ₂ : Trace) (wst_cur : ℚ) (t : ℕ) : ℚ :=
  let wst := τ₁.wst (t+1) - (τ₁.C - τ₂.C) * ↑(t+1)
    if wst_cur > wst then wst_cur else wst

-- Make all propositions decidable
-- open classical
-- local attribute [instance] prop_decidable

-- This is how we derive τₛ.w
def wst_compose (τ₁ τ₂ : Trace) (trackfun: (ℚ → ℕ → ℚ)): ℕ → (ℚ × WstState)
  | 0 => (0, WstState.Tracking)
  | (t + 1) =>
    let ⟨wst, s⟩ := (wst_compose τ₁ τ₂ trackfun t)
    match s with
    | WstState.Tracking =>
      if τ₁.lower (1 + t) ≥ τ₂.upper 1 + t
      then (wst, WstState.NoWst)
      else (trackfun wst t, WstState.Tracking)
    | WstState.NoWst =>
      if τ₂.C * ↑t - wst + τ₂.C ≥ τ₁.upper (1 + t)
      then (trackfun wst t, WstState.Tracking)
      else (wst, WstState.NoWst)

lemma compose_counterexample (IB: InfB): ∃ (τ₁ τ₂: Trace),
  τ₁.C ≥ τ₂.C ∧
  τ₁.out = τ₂.inp ∧
   (∀t, τ₁.los t = 0 ∧ τ₂.los t = 0) ∧
  (∃ (t: ℕ), τ₂.out t > (τ₂.C * t) - (wst_compose τ₁ τ₂ (track_paper τ₁ τ₂) t).fst) ∧
  (∃ (t: ℕ), τ₂.out t > (τ₂.C * t) - (wst_compose τ₁ τ₂ (track_ours τ₁ τ₂) t).fst) := by
  exists (mkt1 IB),(mkt2 IB)
  constructor
  constructor
  constructor
  constructor
  constructor
  . intros t
    constructor <;> simp
  constructor
  all_goals {
    exists 2
    simp [track_paper, track_ours, wst_compose, Trace.lower, Trace.upper, le_refl, Nat.le_step]
    sorry
  }

/-
theorem trace_composes_τ₁_ge_τ₂ :
    ∀(τ₁ τ₂ : Trace),
        τ₁.C ≥ τ₂.C ∧
        τ₁.out = τ₂.inp ∧
        (∀t, τ₁.los t = 0 ∧ τ₂.los t = 0)
    → ∃(τₛ : Trace),
        τₛ.C = τ₁.C ∧
        τₛ.D = τ₁.D + τ₂.D ∧
        τₛ.inp = τ₁.inp ∧
        τₛ.out = τ₂.out ∧
        ∀ t, τₛ.los t = τ₁.los t + τ₂.los t :=
begin
  intros τ₁ τ₂ h, cases h with hc h, cases h with h₁₂ h_los,

  -- We will set τₛ.wst to wst_compose
  -- generalize h : w = λ t, (waste_compose τ₁ τ₂ t),
  -- have h : ℕ → (ℚ × WstState) := (λ t, (wst_compose τ₁ τ₂ t)),
  generalize h_wstₛ : (wst_compose τ₁ τ₂) = wstₛ,

  -- Whenever waste happens, it is allowed
  have h_cond_waste : ∀t, (wstₛ (1 + t)).1 > (wstₛ t).1 →
    τ₁.inp (1 + t) ≤ τ₂.C * (1 + t) - (wstₛ (1 + t)).1 :=
  begin
    intros t h_inc,
    induction t,
    {
      simp, rw <- h_wstₛ, unfold wst_compose,
      by_cases h_cond : ((Trace.lower τ₁ (1 + 0) ≥ Trace.upper τ₂ 1 + ↑0)) = tt,
      rw h_cond,

      sorry
    },
    -- Go through wst_compose and get the cases where waste can increase
    -- rw wstₛ at h_wst,
    sorry,
  end,

  sorry,
end-/

end Compose1Ge2
