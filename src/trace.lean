-- Some obvious theorems I couldn't prove
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Defs
import Mathlib.Tactic.Linarith.Frontend

theorem nat_real_le : ∀(x y : ℕ), x ≤ y → (↑x : ℚ) ≤ (↑y : ℚ) := by sorry

theorem nat_real_add : ∀(x y : ℕ), ↑(x + y) = (↑x : ℚ) + ↑y := by (intros; simp)

theorem nat_real_succ : ∀x:ℕ, (↑(x.succ) : ℚ) = 1 + ↑x := by sorry

theorem nat_real_sub : ∀(x y : ℕ), y ≤ x → ↑(x - y) = (↑x: ℚ) - ↑y := sorry

theorem nat_le_succ_sub : ∀(x y : ℕ), x - y ≤ (x.succ) - y := sorry

theorem nat_sub_add : ∀(x y z : ℕ), x - (y + z) = x - y - z := sorry

structure Trace where
    (C β : ℚ) (D : ℕ) (out inp wst los: ℕ → ℚ)

    (pos_C : C > 0)
    (nonneg_D : D ≥ 0)
    (pos_β : β > 0)

    (constraint_u : ∀t, out t ≤ C * t - wst t)
    (constraint_l : ∀t, out t ≥ C * ↑(t - D) - wst (t - D))

    (cond_waste :
        ∀t, wst t < wst (t + 1)
        → inp (1 + t) - los (1 + t) ≤ C * ↑(1 + t) - wst (1 + t))

    (cond_los :
        ∀t, los t < los (t + 1)
        → inp (1 + t) - los (1 + t) > C * ↑t - wst t + β)

    (max_buf :
        ∀t, inp t - los t ≤ C * ↑t - wst t + β)

    (out_le_inp : ∀t, out t ≤ inp t - los t)

    (monotone_out : Monotone out)
    (monotone_inp : Monotone inp)
    (monotone_wst : Monotone wst)
    (monotone_los : Monotone los)

    (zero_out : out 0 = 0)
    (zero_inp : inp 0 = 0)
    (zero_wst : wst 0 = 0)
    (zero_los : los 0 = 0)

-- Useful lemmas
namespace Trace
    def upper (τ : Trace) (t : ℕ) := τ.C * t - τ.wst t
    def lower (τ : Trace) (t : ℕ) := τ.C * ↑(t - τ.D) - τ.wst (t - τ.D)

    lemma out_nonneg : ∀(τ : Trace), ∀(t : ℕ), 0 ≤ τ.out t := by
      intros τ t
      induction t
      . rw [τ.zero_out]
      . rename_i n ih
        apply (le_trans ih)
        apply τ.monotone_out
        exact n.le_succ

    lemma wst_nonneg : ∀(τ : Trace), ∀(t : ℕ), 0 ≤ τ.wst t := by
      intros τ t
      induction t
      . rw [τ.zero_wst]
      . rename_i n ih
        apply (le_trans ih)
        apply τ.monotone_wst
        exact n.le_succ

    lemma los_nonneg : ∀(τ : Trace), ∀(t : ℕ), 0 ≤ τ.los t := by
      intros τ t
      induction t
      . rw [τ.zero_los]
      . rename_i n ih
        apply (le_trans ih)
        apply τ.monotone_los
        exact n.le_succ

    lemma wst_u_bound :
        ∀(τ : Trace), ∀(t : ℕ), τ.wst t ≤ τ.C * ↑t := by
        intros τ t
        have h_constraint_u := τ.constraint_u t
        have h_out_nonneg := τ.out_nonneg t
        linarith

    theorem black_line_gap :
      ∀τ : Trace, ∀t, τ.upper t - τ.lower t ≤ τ.C * τ.D := by
      intros τ t
      rw [Trace.upper, Trace.lower]
      by_cases h_t_vs_D : t ≤ τ.D
      -- Case: t ≤ τ.D
      . have t_minus_D := Nat.sub_eq_zero_of_le h_t_vs_D
        rw [t_minus_D,τ.zero_wst]
        simp
        have h₀ := (nat_real_le t τ.D h_t_vs_D)
        have h₁ := Trace.wst_nonneg τ t
        have h₂ := τ.pos_C
        have h₃ : 0 ≤ τ.C := by linarith
        have h₃ := mul_le_mul_of_nonneg_left h₀ h₃
        linarith
      -- Case: t > τ.D
      . -- Split ↑(t - τ.D)
        simp at h_t_vs_D
        have h_D_le_t: τ.D ≤ t := by linarith [h_t_vs_D]
        clear h_t_vs_D
        rw [(nat_real_sub t τ.D h_D_le_t)]

        -- Cancel τ.C
        rw [mul_sub]
        have h : τ.wst (t - τ.D) ≤ τ.wst t
          → τ.wst (t - τ.D) + (-τ.wst t + τ.C * ↑(τ.D)) ≤ τ.C * ↑(τ.D) := by
          intro h
          linarith
        have h2 : t - τ.D ≤ t := Nat.sub_le t τ.D
        specialize (h (τ.monotone_wst h2))
        linarith

end Trace
