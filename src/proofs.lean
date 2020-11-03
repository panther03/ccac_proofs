import data.real.basic

-- Some obvious theorems I couldn't prove

theorem nat_real_le : ∀(x y : ℕ), x ≤ y → (↑x : ℝ) ≤ (↑y : ℝ) := sorry

theorem nat_real_succ : ∀x:ℕ, (↑(nat.succ x) : ℝ) = 1 + ↑x := sorry

theorem nat_real_sub : ∀(x y : ℕ), y ≤ x → ↑(x - y) = (↑x: ℝ) - ↑y := sorry

theorem nat_le_succ_sub : ∀(x y : ℕ), x - y ≤ (nat.succ x) - y := sorry

structure Trace :=
(C : ℝ) (D : ℕ) (out inp wst: ℕ → ℝ)

namespace Trace
    def pos_C (τ : Trace) : τ.C > 0 := sorry
    def nonneg_D (τ : Trace) : τ.D ≥ 0 := sorry

    def upper (τ : Trace) (t : ℕ) := τ.C * t - τ.wst t
    def lower (τ : Trace) (t : ℕ) := τ.C * ↑(t - τ.D) - τ.wst (t - τ.D)

    def constraint_u (τ : Trace) :
        ∀t, τ.out t ≤ τ.upper t := sorry    
    def constraint_l (τ : Trace) :
        ∀t, τ.out t ≥ τ.lower t := sorry

    def cond_waste (τ : Trace) :
        ∀t, τ.wst t < τ.wst (t+1) 
        → τ.inp (1 + t) ≤ τ.upper (1 + t) := sorry
    
    def out_le_inp (τ : Trace) :
        ∀t, τ.out t ≤ τ.inp t := sorry
    
    def monotone_out (τ : Trace) : monotone τ.out := sorry
    def monotone_inp (τ : Trace) : monotone τ.inp := sorry
    def monotone_wst (τ : Trace) : monotone τ.wst := sorry

    def zero_out (τ : Trace) : τ.out 0 = 0 := sorry
    def zero_inp (τ : Trace) : τ.inp 0 = 0 := sorry
    def zero_wst (τ : Trace) : τ.wst 0 = 0 := sorry


    lemma out_nonneg : ∀(τ : Trace), ∀(t : ℕ), 0 ≤ τ.out t :=
    begin
        intros τ t,
        induction t,
        rw τ.zero_out, apply (le_trans t_ih), 
        apply τ.monotone_out, exact nat.le_succ t_n,
    end

    lemma wst_nonneg : ∀(τ : Trace), ∀(t : ℕ), 0 ≤ τ.wst t :=
    begin
        intros τ t,
        induction t,
        rw τ.zero_wst, apply (le_trans t_ih), 
        apply τ.monotone_wst, exact nat.le_succ t_n,
    end

    lemma wst_u_bound :
        ∀(τ : Trace), ∀(t : ℕ), τ.wst t ≤ τ.C * ↑t :=
    begin
        intros τ t,
        have h_constraint_u := τ.constraint_u t,
        unfold Trace.upper at h_constraint_u,
        have h_out_nonneg := τ.out_nonneg t,
        linarith,
    end

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
        ∀t, τ₁.lower t ≤ τ₂.upper t :=
    begin
        intro t,
        unfold Trace.lower, unfold Trace.upper,

        induction t,
        -- induction: t = 0
        simp, rw τ₁.zero_wst, rw τ₂.zero_wst,
        --simp, apply mul_nonneg', linarith [τ₁.pos_C], exact h_τ₁_nonneg_D,
        -- induction: t > 0

        by_cases h_t_vs_D : (t_n < τ₁.D),
        -- t_n < τ₁.D
        have h_t_le_D := nat.sub_eq_zero_of_le h_t_vs_D,
        rw h_t_le_D, rw τ₁.zero_wst, simp,
        have h_wst_u_bound := τ₂.wst_u_bound (nat.succ t_n),
        rw (nat_real_succ t_n) at h_wst_u_bound,
        linarith [h_wst_u_bound],

        -- t_n ≥ τ₁.D
        simp at h_t_vs_D,
        have h_τ₁_wst_nondec : τ₁.wst (t_n - τ₁.D) ≤ τ₁.wst (nat.succ t_n - τ₁.D), {
            apply τ₁.monotone_wst, apply nat_le_succ_sub,
        },

        have h_τ₂_wst_nondec: τ₂.wst t_n ≤ τ₂.wst (nat.succ t_n), by sorry,
        have h_τ₂_wst_cond : τ₂.wst t_n = τ₂.wst (nat.succ t_n) ∨ τ₂.wst t_n < τ₂.wst (nat.succ t_n), from (eq_or_lt_of_le h_τ₂_wst_nondec),
        let h_τ₂_constraint_l := τ₁.constraint_l (nat.succ t_n),
        unfold Trace.lower at h_τ₂_constraint_l,

        -- rewrite (t - D) as ↑t - ↑D
        rw (nat_real_sub t_n τ₁.D h_t_vs_D) at t_ih,
        have h_st_vs_D : τ₁.D ≤ 1 + t_n, by linarith [h_t_vs_D],
        rw nat.one_add t_n at h_st_vs_D,
        rw (nat_real_sub (nat.succ t_n) τ₁.D h_st_vs_D),
        rw (nat_real_sub (nat.succ t_n) τ₁.D h_st_vs_D) at h_τ₂_constraint_l,

        cases h_τ₂_wst_cond,
        { -- τ₂.wst does not increase

            rw ←h_τ₂_wst_cond,
            have h_nat_real_t_n : (↑(nat.succ t_n) : ℝ) = 1 + ↑t_n, from nat_real_succ t_n,

            rw (nat_real_succ t_n),

            -- Apply distributive laws. `linarith` cannot infer this
            rw mul_sub at t_ih,
            rw mul_sub, rw mul_add, rw mul_add,
            
            linarith,
        },
        { -- τ₂.wst increases
            -- use τ₂.cond_waste
            let h_cond_waste := τ₂.cond_waste t_n h_τ₂_wst_cond,
            unfold Trace.upper at h_cond_waste,
            rw nat.one_add t_n at h_cond_waste, rw (nat_real_succ t_n) at h_cond_waste,
            -- τ₂'s input is τ₁'s output
            rw ←h₁₂ at h_cond_waste,

            -- Apply distributive laws. `linarith` cannot infer this
            simp, simp at *, rw mul_add at *,

            apply (le_trans h_τ₂_constraint_l), rw mul_add,
            rw ←hc, rw ←hc at *, rw add_comm,
            have : (nat.succ t_n) = t_n + 1, by simp, rw this,
            exact (add_le_add_left h_cond_waste (τ₁.wst (t_n + 1 - τ₁.D))),
        }
    end,

    -- Use h_lower_le_upper to prove constraint_l
    have h_constraint_l :
        ∀t, τ₂.out t ≥ τ₁.C * (t - τ₁.D - τ₂.D) - τ₁.wst (t - τ₁.D - τ₂.D) :=
    begin
        intro t,
        -- Bring in things we already know
        specialize h_lower_le_upper t,
        let h_τ₂_constraint_l := τ₂.constraint_l t,
        let h_τ₁_constraint_l := τ₁.constraint_l (t - τ₂.D),
        let h_τ₁_constraint_u := τ₁.constraint_u (t - τ₂.D),
        rw nat_real_sub at h_τ₁_constraint_l, rw nat_real_sub at h_τ₁_constraint_u,
        let h_τ₁_out_le_inp := τ₁.out_le_inp t,

        -- Apply distributive law everywhere
        rw mul_sub at *, rw mul_sub,

        apply (ge_trans h_τ₂_constraint_l), rw ←hc,

        have h₀ : τ₁.wst (t - τ₂.D) ≤ τ₁.C * ↑(τ₁.D) + τ₁.wst (t - τ₁.D - τ₂.D), 
            by linarith [h_τ₁_constraint_u, h_τ₁_constraint_l],

/-         h_τ₁_constraint_u : τ₁.out t ≤ τ₁.C * ↑t - τ₁.wst t := Trace.constraint_u τ₁ t,
        h_τ₁_out_le_inp : τ₁.out t ≤ τ₁.inp t := Trace.out_le_inp τ₁ t,
        h_τ₂_constraint_l : τ₂.out t ≥ τ₂.C * ↑t - τ₂.C * ↑(τ₂.D) - τ₂.wst (t - τ₂.D),
        h_τ₁_constraint_l : τ₁.out t ≥ τ₁.C * ↑t - τ₁.C * ↑(τ₁.D) - τ₁.wst (t - τ₁.D),
 -/
        sorry,
    end,

    sorry,
end
