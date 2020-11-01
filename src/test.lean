import data.real.basic

theorem nat_real_le : ∀(x y : ℕ), x ≤ y → (↑x : ℝ) ≤ (↑y : ℝ) := sorry

theorem ge_0_le_0 : ∀(x y : ℝ), x - y = x + (-y) :=
begin
    intros x y, linarith,
end 

