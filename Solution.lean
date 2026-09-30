module

public import Minimax

namespace Minimax.Palomar

public theorem maxmin_le_minmax {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (u : A → B → ℝ) : maxminValue u ≤ minmaxValue u := by
  exact Minimax.maxmin_le_minmax u

public theorem minmax_le_maxmin {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (u : A → B → ℝ) : minmaxValue u ≤ maxminValue u := by
  exact Minimax.minmax_le_maxmin u

public theorem minimax_theorem {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (u : A → B → ℝ) : maxminValue u = minmaxValue u := by
  exact Minimax.minimax_theorem u

end Minimax.Palomar
