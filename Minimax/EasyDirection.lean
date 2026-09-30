import Minimax.Basic

/-!
# The easy minimax inequality

The maximizing player's guaranteed payoff is at most the minimizing player's
guaranteed payoff ceiling.
-/

namespace Minimax

variable {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]

/-- The maxmin value is at most the minmax value. -/
theorem maxmin_le_minmax (u : A → B → ℝ) : maxminValue u ≤ minmaxValue u := by
  apply ciSup_le
  intro x
  apply le_ciInf
  intro y
  exact (ciInf_le (bddBelow_payoff_right u x) y).trans
    (le_ciSup (bddAbove_payoff_left u y) x)

end Minimax
