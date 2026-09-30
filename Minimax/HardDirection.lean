import Minimax.EasyDirection
import Mathlib.Topology.Sion
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The hard minimax inequality and von Neumann's minimax theorem

The coordinate simplices are nonempty compact convex sets. The bilinear payoff
satisfies Sion's hypotheses with the minimizing player first. Its saddle point
bounds the minmax value above and the maxmin value below by the same payoff.
-/

namespace Minimax

open scoped BigOperators

/-- Probability vectors as a subset of the ambient real vector space. -/
def coordSimplex (S : Type*) [Fintype S] [Nonempty S] : Set (S → ℝ) :=
  {x | (∀ s, 0 ≤ x s) ∧ ∑ s, x s = 1}

variable {S : Type*} [Fintype S] [Nonempty S]

theorem MixedStrategy.val_mem_coordSimplex (x : MixedStrategy S) :
    x.val ∈ coordSimplex S :=
  ⟨x.nonneg, x.sum_one⟩

/-- Turn a point of the coordinate simplex into a mixed strategy. -/
def MixedStrategy.ofCoordSimplex (x : S → ℝ) (hx : x ∈ coordSimplex S) :
    MixedStrategy S :=
  ⟨x, hx.1, hx.2⟩

@[simp] theorem MixedStrategy.ofCoordSimplex_val (x : S → ℝ)
    (hx : x ∈ coordSimplex S) : (MixedStrategy.ofCoordSimplex x hx).val = x := rfl

theorem coordSimplex_nonempty : (coordSimplex S).Nonempty :=
  ⟨MixedStrategy.uniform.val, MixedStrategy.uniform.val_mem_coordSimplex⟩

theorem convex_coordSimplex : Convex ℝ (coordSimplex S) := by
  intro x hx z hz p q hp hq hpq
  constructor
  · intro s
    exact add_nonneg (mul_nonneg hp (hx.1 s)) (mul_nonneg hq (hz.1 s))
  · change ∑ s, (p * x s + q * z s) = 1
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hx.2, hz.2, mul_one] using hpq

theorem isClosed_coordSimplex : IsClosed (coordSimplex S) := by
  have hnonneg : IsClosed {x : S → ℝ | ∀ s, 0 ≤ x s} := by
    simpa only [Set.ofPred_forall] using
      (isClosed_iInter fun s : S => isClosed_le continuous_const (continuous_apply s))
  have hsum : Continuous (fun x : S → ℝ => ∑ s, x s) :=
    continuous_finsetSum _ (fun s _ => continuous_apply s)
  exact hnonneg.inter (isClosed_eq hsum continuous_const)

theorem isCompact_coordSimplex : IsCompact (coordSimplex S) := by
  have hbox : IsCompact (Set.pi Set.univ (fun _ : S => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  apply hbox.of_isClosed_subset isClosed_coordSimplex
  intro x hx s _
  exact ⟨hx.1 s, (MixedStrategy.ofCoordSimplex x hx).val_le_one s⟩

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The payoff is continuous in the maximizing player's weight vector. -/
theorem continuous_weightedPayoff_left (u : A → B → ℝ) (y : B → ℝ) :
    Continuous (fun x : A → ℝ => weightedPayoff u x y) := by
  unfold weightedPayoff
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro b _
  exact ((continuous_apply a).mul continuous_const).mul continuous_const

/-- The payoff is continuous in the minimizing player's weight vector. -/
theorem continuous_weightedPayoff_right (u : A → B → ℝ) (x : A → ℝ) :
    Continuous (fun y : B → ℝ => weightedPayoff u x y) := by
  unfold weightedPayoff
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro b _
  exact (continuous_const.mul (continuous_apply b)).mul continuous_const

private noncomputable def payoffLeftLinearMap (u : A → B → ℝ) (y : B → ℝ) :
    (A → ℝ) →ₗ[ℝ] ℝ where
  toFun x := weightedPayoff u x y
  map_add' x z := weightedPayoff_add_left u x z y
  map_smul' c x := weightedPayoff_smul_left u c x y

private noncomputable def payoffRightLinearMap (u : A → B → ℝ) (x : A → ℝ) :
    (B → ℝ) →ₗ[ℝ] ℝ where
  toFun y := weightedPayoff u x y
  map_add' y z := weightedPayoff_add_right u x y z
  map_smul' c y := weightedPayoff_smul_right u c x y

variable [Nonempty A] [Nonempty B]

/-- Sion supplies optimal mixed strategies with a common saddle payoff. -/
theorem exists_payoff_saddle (u : A → B → ℝ) :
    ∃ x : MixedStrategy A, ∃ y : MixedStrategy B,
      ∀ x' : MixedStrategy A, ∀ y' : MixedStrategy B,
        expPayoff u x' y ≤ expPayoff u x y' := by
  obtain ⟨y, hy, x, hx, hsaddle⟩ := Sion.exists_isSaddlePointOn
    (f := fun y x => weightedPayoff u x y)
    (coordSimplex_nonempty (S := B)) convex_coordSimplex isCompact_coordSimplex
    (fun x _ => (continuous_weightedPayoff_right u x).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun x _ => ((payoffRightLinearMap u x).convexOn convex_coordSimplex).quasiconvexOn)
    convex_coordSimplex (coordSimplex_nonempty (S := A)) isCompact_coordSimplex
    (fun y _ => (continuous_weightedPayoff_left u y).upperSemicontinuous.upperSemicontinuousOn _)
    (fun y _ => ((payoffLeftLinearMap u y).concaveOn convex_coordSimplex).quasiconcaveOn)
  refine ⟨MixedStrategy.ofCoordSimplex x hx, MixedStrategy.ofCoordSimplex y hy, ?_⟩
  intro x' y'
  exact hsaddle y'.val y'.val_mem_coordSimplex x'.val x'.val_mem_coordSimplex

/-- The minmax value is at most the maxmin value. -/
theorem minmax_le_maxmin (u : A → B → ℝ) : minmaxValue u ≤ maxminValue u := by
  obtain ⟨x, y, hsaddle⟩ := exists_payoff_saddle u
  have hminmax : minmaxValue u ≤ expPayoff u x y := by
    apply (ciInf_le (bddBelow_iSup_payoff u) y).trans
    exact ciSup_le (fun x' => hsaddle x' y)
  have hmaxmin : expPayoff u x y ≤ maxminValue u := by
    apply le_trans _ (le_ciSup (bddAbove_iInf_payoff u) x)
    exact le_ciInf (fun y' => hsaddle x y')
  exact hminmax.trans hmaxmin

/-- Von Neumann's minimax theorem for finite nonempty strategy spaces. -/
theorem minimax_theorem (u : A → B → ℝ) : maxminValue u = minmaxValue u :=
  le_antisymm (maxmin_le_minmax u) (minmax_le_maxmin u)

end Minimax
