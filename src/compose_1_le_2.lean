import data.real.basic
import data.bool

import trace

-- Some obvious theorems I couldn't prove

theorem no_loss_τ₁_le_τ₂ :
  ∀(τ₁ τ₂ : Trace),
    τ₁.C ≤ τ₂.C ∧
    τ₂.β ≥ τ₁.C * τ₁.D + τ₁.C ∧
    τ₁.out = τ₂.inp
  → ∀t, τ₂.los t = 0 :=
begin
  intros τ₁ τ₂ h, cases h with hc h, cases h with hβ h₁₂,
  have h_loss_cond :
  ∀t,
    τ₂.los t = 0 ∧
    τ₁.lower t ≤ τ₂.upper t :=
  begin
    intro t,
    induction t,
    {
      apply and.intro, apply τ₂.zero_los,
      -- rw τ₂.zero_inp, rw τ₂.zero_los, rw τ₂.zero_wst,

      -- apply and.intro,
      -- simp, linarith [τ₂.pos_β],

      rw Trace.lower, rw Trace.upper, simp,
      rw τ₁.zero_wst, rw τ₂.zero_wst,
    },
    {
      cases t_ih with t_ih_zero t_ih_bound,
      split,
      show τ₂.los (nat.succ t_n) = 0,
      begin
        -- Contradiction when τ₂.los did increase
        -- cases (τ₂.los (nat.succ t_n) = 0),
        have h₀ := lt_trichotomy (τ₂.los (nat.succ t_n)) 0, cases h₀,
        { -- los < 0, trivial contradiction
          exfalso, have h₁ := τ₂.los_nonneg (nat.succ t_n),
          have h₂ := (lt_iff_not_ge (τ₂.los (nat.succ t_n)) 0),
          have h₃ := (h₂.elim_left h₀),
          apply (h₃ h₁),
        },
        cases h₀,
        { -- los = 0
          apply h₀
        },
        { -- los > 0, the main case
          exfalso,

          -- apply cond_los
          rw <- t_ih_zero at h₀,
          have h_contra := τ₂.cond_los t_n h₀, clear h₀,

          -- Fold τ₂.upper
          have h₂ : τ₂.upper t_n = τ₂.C * ↑t_n - τ₂.wst t_n :=
          begin unfold Trace.upper, end,
          rw <- h₂ at h_contra, clear h₂,

          -- Manipulate t_ih_bound to contradict with h_contra
          have h₁ : τ₁.lower t_n + τ₁.C * ↑τ₁.D + τ₁.C ≤ τ₂.upper t_n + τ₂.β :=
          begin linarith, end,

          have h₂ : τ₁.upper t_n + τ₁.C ≤ τ₂.upper t_n + τ₂.β :=
          begin have h₃ := Trace.black_line_gap τ₁ t_n, linarith, end,

          have h₃ : τ₁.upper (1 + t_n) ≤ τ₂.upper t_n + τ₂.β :=
          begin
            unfold Trace.upper, unfold Trace.upper at h₂,
            rw nat_real_add, rw mul_add, simp,
            have h₄ : τ₁.wst (t_n + 1) ≥ τ₁.wst t_n :=
            begin apply τ₁.monotone_wst, linarith, end,
            linarith,
          end,

          have h₄ := τ₁.constraint_u (1 + t_n),
          rw h₁₂ at h₄,
          have h₅ : τ₂.inp (1 + t_n) ≤ Trace.upper τ₁ (1 + t_n) :=
          begin unfold Trace.upper, exact h₄, end,
          -- have h₆ := le_trans (τ₂.inp (1 + t_n)) (τ₁.upper (1 + t_n)) (Trace.upper τ₂ t_n + τ₂.β),
          have h₆ := le_trans h₅ h₃,

          have h₇ : τ₂.inp (1 + t_n) - τ₂.los (1 + t_n) ≤ Trace.upper τ₂ t_n + τ₂.β :=
          begin have h₈ := τ₂.los_nonneg (1 + t_n), linarith, end,
          have h₈ := not_lt.elim_right h₇,
          apply h₈ h_contra,
        }
      end,

      show τ₁.lower (nat.succ t_n) ≤ τ₂.upper (nat.succ t_n),
      begin
        sorry,
      end,
    }
  end,
  sorry,
end

-- Prove lower of τ₁ ≤ upper of τ₂ by induction on t
theorem lower_le_upper :
  ∀(τ₁ τ₂ : Trace),
    τ₁.C ≤ τ₂.C ∧
    τ₁.out = τ₂.inp
    → ∀t, τ₁.lower t ≤ τ₂.upper t :=
begin
  intros τ₁ τ₂ h, cases h with hc h₁₂,
  intro t,
  unfold Trace.lower, unfold Trace.upper,

  induction t,
  -- induction: t = 0
  simp, rw τ₁.zero_wst, rw τ₂.zero_wst,

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

  have h_τ₂_wst_nondec: τ₂.wst t_n ≤ τ₂.wst (nat.succ t_n),
      { apply τ₂.monotone_wst, exact nat.le_succ t_n, },
  have h_τ₂_wst_cond : τ₂.wst t_n = τ₂.wst (nat.succ t_n) ∨ τ₂.wst t_n  < τ₂.wst (nat.succ t_n), from (eq_or_lt_of_le h_τ₂_wst_nondec),
    let h_τ₂_constraint_l := τ₁.constraint_l (nat.succ t_n),

    -- rewrite (t - D) as ↑t - ↑D
    rw (nat_real_sub t_n τ₁.D h_t_vs_D) at t_ih,
    have h_st_vs_D : τ₁.D ≤ 1 + t_n, by linarith [h_t_vs_D],
    rw nat.one_add t_n at h_st_vs_D,
    rw (nat_real_sub (nat.succ t_n) τ₁.D h_st_vs_D),
    rw (nat_real_sub (nat.succ t_n) τ₁.D h_st_vs_D) at h_τ₂_constraint_l,

    cases h_τ₂_wst_cond,
    { -- τ₂.wst does not increase

      rw ←h_τ₂_wst_cond,
      have h_nat_real_t_n : (↑(nat.succ t_n) : ℚ) = 1 + ↑t_n, from nat_real_succ t_n,

      rw (nat_real_succ t_n),

      -- Apply distributive laws. `linarith` cannot infer this
      rw mul_sub at t_ih,
      rw mul_sub, rw mul_add, rw mul_add,

      linarith,
    },
    { -- τ₂.wst increases
      -- use τ₂.cond_waste
      let h_cond_waste := τ₂.cond_waste t_n h_τ₂_wst_cond,
      rw nat.one_add t_n at h_cond_waste, rw (nat_real_succ t_n) at h_cond_waste,
      -- τ₂'s input is τ₁'s output
      rw ←h₁₂ at h_cond_waste,

      -- Apply distributive laws. `linarith` cannot infer this
      simp, simp at *, rw mul_add at *,

      apply (le_trans h_τ₂_constraint_l), rw mul_add,
      rw add_comm,
      -- have : (nat.succ t_n) = t_n + 1, by simp, rw this,
      exact (add_le_add_left h_cond_waste (τ₁.wst (t_n + 1 - τ₁.D))),
    },
end


theorem trace_composes_τ₁_le_τ₂ :
    ∀(τ₁ τ₂ : Trace),
        τ₁.C ≤ τ₂.C ∧
        τ₁.out = τ₂.inp
    → ∃(τₛ : Trace),
        τₛ.C = τ₁.C ∧
        τₛ.D = τ₁.D + τ₂.D ∧
        τₛ.inp = τ₁.inp ∧
        τₛ.out = τ₂.out :=
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
    have h_τ₁_nonneg_D : 0 ≤ (↑τ₁.D : ℚ), from (nat_real_le 0 τ₁.D τ₁.nonneg_D),
    have h_τ₂_nonneg_D : 0 ≤ (↑τ₂.D : ℚ), from (nat_real_le 0 τ₂.D τ₂.nonneg_D),


    -- Prove lower of τ₁ ≤ upper of τ₂ by induction on t
    have h_lower_le_upper :
        ∀t, τ₁.lower t ≤ τ₂.upper t :=
    begin
        intro t,
        unfold Trace.lower, unfold Trace.upper,

        induction t,
        -- induction: t = 0
        simp, rw τ₁.zero_wst, rw τ₂.zero_wst,

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

        have h_τ₂_wst_nondec: τ₂.wst t_n ≤ τ₂.wst (nat.succ t_n),
            { apply τ₂.monotone_wst, exact nat.le_succ t_n, },
        have h_τ₂_wst_cond : τ₂.wst t_n = τ₂.wst (nat.succ t_n) ∨ τ₂.wst t_n < τ₂.wst (nat.succ t_n), from (eq_or_lt_of_le h_τ₂_wst_nondec),
        let h_τ₂_constraint_l := τ₁.constraint_l (nat.succ t_n),

        -- rewrite (t - D) as ↑t - ↑D
        rw (nat_real_sub t_n τ₁.D h_t_vs_D) at t_ih,
        have h_st_vs_D : τ₁.D ≤ 1 + t_n, by linarith [h_t_vs_D],
        rw nat.one_add t_n at h_st_vs_D,
        rw (nat_real_sub (nat.succ t_n) τ₁.D h_st_vs_D),
        rw (nat_real_sub (nat.succ t_n) τ₁.D h_st_vs_D) at h_τ₂_constraint_l,

        cases h_τ₂_wst_cond,
        { -- τ₂.wst does not increase

            rw ←h_τ₂_wst_cond,
            have h_nat_real_t_n : (↑(nat.succ t_n) : ℚ) = 1 + ↑t_n, from nat_real_succ t_n,

            rw (nat_real_succ t_n),

            -- Apply distributive laws. `linarith` cannot infer this
            rw mul_sub at t_ih,
            rw mul_sub, rw mul_add, rw mul_add,

            linarith,
        },
        { -- τ₂.wst increases
            -- use τ₂.cond_waste
            let h_cond_waste := τ₂.cond_waste t_n h_τ₂_wst_cond,
            rw nat.one_add t_n at h_cond_waste, rw (nat_real_succ t_n) at h_cond_waste,
            -- τ₂'s input is τ₁'s output
            rw ←h₁₂ at h_cond_waste,

            -- Apply distributive laws. `linarith` cannot infer this
            simp, simp at *, rw mul_add at *,

            apply (le_trans h_τ₂_constraint_l), rw mul_add,
            rw add_comm,
            have : (nat.succ t_n) = t_n + 1, by simp, rw this,
            exact (add_le_add_left h_cond_waste (τ₁.wst (t_n + 1 - τ₁.D))),
        }
    end,

    -- Use h_lower_le_upper to prove constraint_l
    have h_constraint_l :
        ∀t, τ₂.out t ≥ τ₁.C * (t - (τ₁.D + τ₂.D)) - τ₁.wst (t - (τ₁.D + τ₂.D)) :=
    begin
        intro t,
        by_cases h_t_vs_D : (t ≤ τ₁.D + τ₂.D),
        -- Case: t < τ₁.D + τ₂.D
        have h_t_le_D := nat.sub_eq_zero_of_le h_t_vs_D,
        rw h_t_le_D, rw τ₁.zero_wst, simp,
        have h_wst_u_bound := τ₂.wst_u_bound (nat.succ t),
        let h_t_vs_D := nat_real_le _ _ h_t_vs_D,
        rw nat_real_add at h_t_vs_D,
        let h_τ₂_C_pos := τ₁.pos_C,
        have h₀ : ↑t + (-(↑τ₁.D : ℚ) + -↑(τ₂.D)) ≤ 0, by linarith,
        have h₁ : τ₁.C * (↑t + (-(↑τ₁.D : ℚ) + -↑(τ₂.D))) ≤ 0,
            by exact linarith.mul_nonpos h₀ h_τ₂_C_pos,
        apply (le_trans h₁),
        apply (τ₂.out_nonneg t),

        -- Case: t ≥ τ₁.D + τ₂.D
        simp at h_t_vs_D,
        -- Bring in things we already know
        specialize h_lower_le_upper (t - τ₂.D),
        let h_τ₂_constraint_l := τ₂.constraint_l t,
        let h_τ₁_constraint_l := τ₁.constraint_l (t - τ₂.D),
        let h_τ₁_constraint_u := τ₁.constraint_u (t - τ₂.D),
        unfold Trace.upper at *,
        unfold Trace.lower at *,
        rw ←nat_sub_add at h_τ₁_constraint_l,
        rw nat_real_sub at h_τ₁_constraint_l, rw nat_real_add at h_τ₁_constraint_l,
        rw nat_real_sub at h_τ₁_constraint_u,
        let h_τ₁_out_le_inp := τ₁.out_le_inp t,

        apply (ge_trans h_τ₂_constraint_l),
        clear h_τ₂_constraint_l,

        have h_t_ge_τ₂_D : τ₂.D ≤ t, by linarith,
        rw (nat_real_sub _ _ h_t_ge_τ₂_D), rw (nat_real_sub _ _ h_t_ge_τ₂_D) at *,
        rw ←nat_sub_add at h_lower_le_upper,

        rw add_comm at h_t_vs_D,
        let h_t_vs_D := le_of_lt h_t_vs_D,
        rw (nat_real_sub t (τ₂.D + τ₁.D) h_t_vs_D) at h_lower_le_upper,
        rw nat.add_comm, rw nat_sub_add,

        rw nat_sub_add at h_lower_le_upper,

        -- Apply distributive law everywhere
        rw nat_real_add at *,
        rw mul_sub at *, rw mul_sub at *, rw mul_add at *,

        linarith,

        -- Now main part of the proof is done. Tie up some loose ends
        linarith, linarith,
    end,
    -- Proved a slightly different version above. Fix it now
    have h_constraint_l : ∀ (t : ℕ), τ₂.out t ≥ τ₁.C * ↑(t - (τ₁.D + τ₂.D)) - τ₁.wst (t - (τ₁.D + τ₂.D)) :=
    begin
        intro t, specialize (h_constraint_l t),
        rw ←nat_real_add at h_constraint_l,

        by_cases h_t_vs_D : t ≤ τ₁.D + τ₂.D,
        -- Case: t ≤ τ₁.D + τ₂.D
        let h₀ := nat.sub_eq_zero_of_le h_t_vs_D,
        rw h₀, simp, rw τ₁.zero_wst,
        rw neg_zero,
        exact (τ₂.out_nonneg t),

        -- Case: t > τ₁.D + τ₂.D
        simp at h_t_vs_D,
        let h₀ := le_of_lt h_t_vs_D,
        let h₁ := (nat_real_sub _ _ h₀),
        rw h₁,
        exact h_constraint_l,
    end,

    -- Now prove some of the little theorems
    have h_out_le_inp : ∀t, τ₂.out t ≤ τ₁.inp t, {
        intro t,
        apply (le_trans (τ₂.out_le_inp t)),
        rw ←h₁₂,
        exact (τ₁.out_le_inp t),
    },

    have h_τₛ_nonneg_D : τ₁.D + τ₂.D ≥ 0,
        by linarith [τ₁.nonneg_D, τ₂.nonneg_D],

    -- Finally construct our witness
    let τₛ := Trace.mk τ₁.C (τ₁.D + τ₂.D) τ₂.out τ₁.inp τ₁.wst
        τ₁.pos_C h_τₛ_nonneg_D
        h_constraint_u
        h_constraint_l
        τ₁.cond_waste
        h_out_le_inp
        τ₂.monotone_out
        τ₁.monotone_inp
        τ₁.monotone_wst
        τ₂.zero_out
        τ₁.zero_inp
        τ₁.zero_wst,
    existsi τₛ,
    repeat {split, reflexivity},
    reflexivity,
end
