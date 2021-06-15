import data.real.basic
import data.bool

import trace

namespace Compose1Ge2

inductive WstState
  | Tracking
  | NoWst

-- Helper function. If (τₛ.w (t+1)) = this value, then τₛ.upper = τ₁.upper
def track (τ₁ τ₂ : Trace) (wst_cur : ℚ) (t : ℕ) : ℚ :=
  let wst := τ₁.wst (t+1) - (τ₁.C - τ₂.C) * ↑t in
    if wst_cur > wst then wst_cur else wst

-- Make all propositions decidable
-- open classical
-- local attribute [instance] prop_decidable

-- This is how we derive τₛ.w
def wst_compose (τ₁ τ₂ : Trace) : ℕ → (ℚ × WstState)
  | 0 := (0, WstState.Tracking)
  | (nat.succ t) :=
    let ⟨wst, s⟩ := (wst_compose t) in
    match s with
    | WstState.Tracking :=
      if τ₁.lower (1 + t) ≥ τ₂.upper 1 + t
      then (wst, WstState.NoWst)
      else (track τ₁ τ₂ wst t, WstState.Tracking)
    | WstState.NoWst :=
      if τ₂.C * ↑t - wst + τ₂.C ≥ τ₁.upper (1 + t)
      then (track τ₁ τ₂ wst t, WstState.Tracking)
      else (wst, WstState.NoWst)
    end

set_option trace.check true
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
end

end Compose1Ge2
