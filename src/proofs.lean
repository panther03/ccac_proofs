import data.real.basic

theorem nat_real_le : ∀(x y : ℕ), x ≤ y → (↑x : ℝ) ≤ (↑y : ℝ) := sorry

structure Trace :=
(C : ℝ) (D : ℕ) (out inp wst: ℕ → ℝ)

namespace Trace
    def pos_C (τ : Trace) : τ.C > 0 := sorry
    def nonneg_D (τ : Trace) : τ.D ≥ 0 := sorry

    def constraint_u (τ : Trace) :
        ∀t, τ.out t ≤ τ.C * t - τ.wst t := sorry
    
    def constraint_l (τ : Trace) :
        ∀t, τ.out t ≥ τ.C * (t - τ.D) - τ.wst (t - τ.D) := sorry

    def cond_waste (τ : Trace) :
        ∀t, τ.wst t < τ.wst (t+1) 
        → τ.inp (t+1) ≤ τ.C * (t+1) - τ.wst (t+1) := sorry
    
    def out_le_inp (τ : Trace) :
        ∀t, τ.out t ≤ τ.inp t := sorry
    
    def monotone_out (τ : Trace) : monotone τ.out := sorry
    def monotone_inp (τ : Trace) : monotone τ.inp := sorry
    def monotone_wst (τ : Trace) : monotone τ.wst := sorry

    def zero_out (τ : Trace) : τ.out 0 = 0 := sorry
    def zero_inp (τ : Trace) : τ.inp 0 = 0 := sorry
    def zero_wst (τ : Trace) : τ.wst 0 = 0 := sorry
end Trace

theorem trace_composes :
    ∀(τ₁ τ₂ : Trace),
        τ₁.C = τ₂.C ∧
        τ₁.out = τ₂.inp
    → ∃(τₛ : Trace),
        τₛ.C = τ₁.C ∧
        τₛ.D = τ₁.D + τ₁.D ∧
        τₛ.inp = τ₁.inp ∧
        τₛ.out = τ₁.out :=
begin
    intros τ₁ τ₂ h, cases h with hc h₁₂,
    -- We will set τₛ.wst = τ₁.wst. Let's start proving the theorems 
    -- we need when we finally make the existential quantifier

    -- constraint_u
    have h_constraint_u : ∀t, τ₂.out t ≤ τ₁.C * t - τ₁.wst t :=
    begin
        intro t,
        calc
            τ₂.out t ≤ τ₂.inp t : τ₂.out_le_inp t
                 ... = τ₁.out t : by rw h₁₂
                 ... ≤ τ₁.C * t - τ₁.wst t : τ₁.constraint_u t
    end,

    -- helpful lemmas: Ds are non-negative
    have h_τ₁_nonneg_D : 0 ≤ (↑τ₁.D : ℝ), from (nat_real_le 0 τ₁.D τ₁.nonneg_D),
    have h_τ₂_nonneg_D : 0 ≤ (↑τ₂.D : ℝ), from (nat_real_le 0 τ₂.D τ₂.nonneg_D),


    -- Prove lower of τ₁ ≤ upper of τ₂ by induction on t
    have h_lower_le_upper :
        ∀t, τ₁.C * (↑t - ↑τ₁.D) - τ₁.wst (t - τ₁.D)
            ≤ τ₁.C * ↑t - τ₂.wst t :=
    begin
        intro t,
        induction t,
        -- induction: t = 0
        simp, rw τ₁.zero_wst, rw τ₂.zero_wst,
        simp, apply mul_nonneg', linarith [τ₁.pos_C], exact h_τ₁_nonneg_D,
        -- induction: t > 0

        have h_nat_real_succ : ∀x:ℕ, (↑(nat.succ x) : ℝ) = 1 + ↑x, sorry,
        have h_τ₁_wst_nondec : τ₁.wst (t_n - τ₁.D) ≤ τ₁.wst (nat.succ t_n - τ₁.D), by sorry,

        have h_τ₂_wst_nondec: τ₂.wst t_n ≤ τ₂.wst (nat.succ t_n), by sorry,
        have h_τ₂_wst_cond : τ₂.wst t_n = τ₂.wst (nat.succ t_n) ∨ τ₂.wst t_n < τ₂.wst (nat.succ t_n), from (eq_or_lt_of_le h_τ₂_wst_nondec),
        cases h_τ₂_wst_cond,
        { -- τ₂.wst does not increase
            rw ←h_τ₂_wst_cond,
            have h_nat_real_t_n : (↑(nat.succ t_n) : ℝ) = 1 + ↑t_n, from h_nat_real_succ t_n,
            rw (h_nat_real_succ t_n),

            -- Apply distributive laws. `linarith` cannot infer this
            rw mul_sub at t_ih,
            rw mul_sub, rw mul_add, 
            
            linarith,
        },
        { -- τ₂.wst increases
            -- use τ₂.cond_waste
            let h_cond_waste := τ₂.cond_waste t_n h_τ₂_wst_cond,
            -- τ₂'s input is τ₁'s output
            rw ←h₁₂ at h_cond_waste,
            -- use τ₁.constraint_l
            let h_constraint_l := τ₁.constraint_l (nat.succ t_n),

            -- Apply distributive laws. `linarith` cannot infer this
            simp, simp at *, rw mul_add at *, 
            --rw mul_sub,

            apply (le_trans h_constraint_l), rw mul_add,
            rw hc, rw add_comm,
            have : (nat.succ t_n) = t_n + 1, by simp, rw this,
            exact (add_le_add_left h_cond_waste (τ₁.wst (t_n + 1 - τ₁.D))),
        }
    end,

    sorry
end
