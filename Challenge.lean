module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

public section

namespace Minimax

open scoped BigOperators

/-- A probability vector on a finite nonempty pure-strategy type. -/
structure MixedStrategy (A : Type*) [Fintype A] [Nonempty A] where
  val : A → ℝ
  nonneg : ∀ a, 0 ≤ val a
  sum_one : ∑ a, val a = 1

noncomputable def expPayoff {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (u : A → B → ℝ) (x : MixedStrategy A) (y : MixedStrategy B) : ℝ :=
  sorry

noncomputable def maxminValue {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (u : A → B → ℝ) : ℝ :=
  sorry

noncomputable def minmaxValue {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (u : A → B → ℝ) : ℝ :=
  sorry

namespace Palomar

public theorem maxmin_le_minmax {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (u : A → B → ℝ) : maxminValue u ≤ minmaxValue u := by
  sorry

public theorem minmax_le_maxmin {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (u : A → B → ℝ) : minmaxValue u ≤ maxminValue u := by
  sorry

public theorem minimax_theorem {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (u : A → B → ℝ) : maxminValue u = minmaxValue u := by
  sorry

end Palomar

end Minimax
