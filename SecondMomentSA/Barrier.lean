module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith

public section

open Filter
open scoped BigOperators

namespace SecondMomentSA

/-- Persistent negative drift above a lower threshold eventually traps a nonnegative sequence
below the upper threshold, provided a step from below the lower threshold stays below the upper
threshold. -/
theorem eventually_lt_of_drift (d α : ℕ → ℝ) (lo hi κ : ℝ)
    (hκ : 0 < κ) (ha : ∀ n, 0 ≤ α n) (hdiv : ¬ Summable α)
    (hdown : ∀ᶠ n in atTop, lo ≤ d n → d (n + 1) ≤ d n - κ * α n)
    (hup : ∀ᶠ n in atTop, d n < lo → d (n + 1) < hi)
    (hlohi : lo < hi) (hd : ∀ n, 0 ≤ d n) : ∀ᶠ n in atTop, d n < hi := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hdown.and hup)
  have hcross : ∃ n, N ≤ n ∧ d n < lo := by
    by_contra! h
    have htel : ∀ m, d (N + m) + κ * (∑ i ∈ Finset.range m, α (i + N)) ≤ d N := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm =>
          have hm : N ≤ N + m := Nat.le_add_right N m
          have hstep := (hN (N + m) hm).1 (h (N + m) hm)
          rw [Finset.sum_range_succ, mul_add, Nat.add_succ, Nat.add_comm m N]
          linarith
    have htail : ¬ Summable (fun i => α (i + N)) :=
      fun hs => hdiv ((summable_nat_add_iff N).mp hs)
    have hsum := (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun i => ha (i + N))).mp htail
    obtain ⟨m, hm⟩ := (tendsto_atTop.1 hsum ((d N + 1) / κ)).exists
    have hlarge := (div_le_iff₀ hκ).mp hm
    linarith [htel m, hd (N + m)]
  obtain ⟨m, hm, hdm⟩ := hcross
  refine eventually_atTop.mpr ⟨m, ?_⟩
  intro n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact hdm.trans hlohi
  | succ n hmn ih =>
      obtain hlow | hhigh := lt_or_ge (d n) lo
      · exact (hN n (hm.trans hmn)).2 hlow
      · exact ((hN n (hm.trans hmn)).1 hhigh).trans_lt
          ((sub_le_self _ (mul_nonneg hκ.le (ha n))).trans_lt ih)

end SecondMomentSA
