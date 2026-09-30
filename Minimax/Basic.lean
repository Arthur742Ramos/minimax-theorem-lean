module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Tactic.Ring

/-!
# Finite mixed strategies and expected payoff

The payoff extends to a bilinear form on arbitrary real weight vectors. The
strategy simplex is closed under convex combinations, on which payoff is affine.
All real infima and suprema used in the value definitions have bounded ranges.
-/

namespace Minimax

open scoped BigOperators

/-- A probability vector on a finite nonempty pure-strategy type. -/
public structure MixedStrategy (A : Type*) [Fintype A] [Nonempty A] where
  val : A → ℝ
  nonneg : ∀ a, 0 ≤ val a
  sum_one : ∑ a, val a = 1

namespace MixedStrategy

variable {A : Type*} [Fintype A] [Nonempty A]

@[ext] public theorem ext {x y : MixedStrategy A} (h : ∀ a, x.val a = y.val a) : x = y := by
  cases x
  cases y
  congr
  exact funext h

/-- The uniform distribution witnesses nonemptiness without choosing a vertex. -/
@[expose] public noncomputable def uniform : MixedStrategy A where
  val _ := (Fintype.card A : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero))

public instance instNonempty : Nonempty (MixedStrategy A) := ⟨uniform⟩

@[simp] public theorem uniform_val (a : A) : (uniform : MixedStrategy A).val a =
    (Fintype.card A : ℝ)⁻¹ := rfl

public theorem val_le_one (x : MixedStrategy A) (a : A) : x.val a ≤ 1 := by
  rw [← x.sum_one]
  exact Finset.single_le_sum (fun b _ => x.nonneg b) (Finset.mem_univ a)

/-- A convex combination, with explicit nonnegative coefficients summing to one. -/
@[expose] public noncomputable def mix (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (x z : MixedStrategy A) : MixedStrategy A where
  val a := p * x.val a + q * z.val a
  nonneg a := add_nonneg (mul_nonneg hp (x.nonneg a)) (mul_nonneg hq (z.nonneg a))
  sum_one := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, x.sum_one, z.sum_one, mul_one]
    exact hpq

@[simp] public theorem mix_val (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (x z : MixedStrategy A) (a : A) :
    (mix p q hp hq hpq x z).val a = p * x.val a + q * z.val a := rfl

end MixedStrategy

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Bilinear extension of the payoff to unrestricted real weight vectors. -/
@[expose] public noncomputable def weightedPayoff (u : A → B → ℝ) (x : A → ℝ) (y : B → ℝ) : ℝ :=
  ∑ a, ∑ b, x a * y b * u a b

public theorem weightedPayoff_add_left (u : A → B → ℝ) (x z : A → ℝ) (y : B → ℝ) :
    weightedPayoff u (x + z) y = weightedPayoff u x y + weightedPayoff u z y := by
  simp [weightedPayoff, add_mul, Finset.sum_add_distrib]

public theorem weightedPayoff_smul_left (u : A → B → ℝ) (c : ℝ) (x : A → ℝ) (y : B → ℝ) :
    weightedPayoff u (c • x) y = c * weightedPayoff u x y := by
  simp [weightedPayoff, mul_assoc, Finset.mul_sum]

public theorem weightedPayoff_add_right (u : A → B → ℝ) (x : A → ℝ) (y z : B → ℝ) :
    weightedPayoff u x (y + z) = weightedPayoff u x y + weightedPayoff u x z := by
  simp [weightedPayoff, mul_add, add_mul, Finset.sum_add_distrib]

public theorem weightedPayoff_smul_right (u : A → B → ℝ) (c : ℝ) (x : A → ℝ) (y : B → ℝ) :
    weightedPayoff u x (c • y) = c * weightedPayoff u x y := by
  simp only [weightedPayoff, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

variable [Nonempty A] [Nonempty B]

/-- Expected payoff of a pair of mixed strategies. -/
@[expose] public noncomputable def expPayoff (u : A → B → ℝ) (x : MixedStrategy A)
    (y : MixedStrategy B) : ℝ :=
  ∑ a, ∑ b, x.val a * y.val b * u a b

public theorem expPayoff_eq_weightedPayoff (u : A → B → ℝ) (x : MixedStrategy A)
    (y : MixedStrategy B) : expPayoff u x y = weightedPayoff u x.val y.val := rfl

/-- Linearity on coordinates whenever the resulting vector is a mixed strategy. -/
public theorem expPayoff_linear_left (u : A → B → ℝ) (x z w : MixedStrategy A)
    (y : MixedStrategy B) (p q : ℝ)
    (hw : ∀ a, w.val a = p * x.val a + q * z.val a) :
    expPayoff u w y = p * expPayoff u x y + q * expPayoff u z y := by
  have h : w.val = p • x.val + q • z.val := funext hw
  simp only [expPayoff_eq_weightedPayoff, h, weightedPayoff_add_left,
    weightedPayoff_smul_left]

public theorem expPayoff_linear_right (u : A → B → ℝ) (x : MixedStrategy A)
    (y z w : MixedStrategy B) (p q : ℝ)
    (hw : ∀ b, w.val b = p * y.val b + q * z.val b) :
    expPayoff u x w = p * expPayoff u x y + q * expPayoff u x z := by
  have h : w.val = p • y.val + q • z.val := funext hw
  simp only [expPayoff_eq_weightedPayoff, h, weightedPayoff_add_right,
    weightedPayoff_smul_right]

public theorem expPayoff_mix_left (u : A → B → ℝ) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (x z : MixedStrategy A) (y : MixedStrategy B) :
    expPayoff u (MixedStrategy.mix p q hp hq hpq x z) y =
      p * expPayoff u x y + q * expPayoff u z y :=
  expPayoff_linear_left u x z _ y p q (fun _ => rfl)

public theorem expPayoff_mix_right (u : A → B → ℝ) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (x : MixedStrategy A) (y z : MixedStrategy B) :
    expPayoff u x (MixedStrategy.mix p q hp hq hpq y z) =
      p * expPayoff u x y + q * expPayoff u x z :=
  expPayoff_linear_right u x y z _ p q (fun _ => rfl)

/-- The pure strategy concentrated at one vertex. -/
@[expose] public noncomputable def pure (a : A) : MixedStrategy A := by
  classical
  refine ⟨fun a' => if a' = a then 1 else 0, ?_, ?_⟩
  · intro a'
    split
    · exact zero_le_one
    · exact le_rfl
  · simp

open Classical in
@[simp] public theorem pure_val (a a' : A) : (pure a).val a' = if a' = a then 1 else 0 := by
  classical
  rfl

@[simp] public theorem expPayoff_pure_left (u : A → B → ℝ) (a : A) (y : MixedStrategy B) :
    expPayoff u (pure a) y = ∑ b, y.val b * u a b := by
  classical
  simp [expPayoff, pure_val, ite_mul]

@[simp] public theorem expPayoff_pure_right (u : A → B → ℝ) (x : MixedStrategy A) (b : B) :
    expPayoff u x (pure b) = ∑ a, x.val a * u a b := by
  classical
  simp [expPayoff, pure_val, mul_ite, ite_mul]

@[simp] public theorem expPayoff_pure_pure (u : A → B → ℝ) (a : A) (b : B) :
    expPayoff u (pure a) (pure b) = u a b := by
  classical
  simp [pure_val, ite_mul]

@[simp] public theorem expPayoff_const (c : ℝ) (x : MixedStrategy A) (y : MixedStrategy B) :
    expPayoff (fun _ _ => c) x y = c := by
  simp only [expPayoff, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul,
    y.sum_one, x.sum_one, one_mul]

public theorem expPayoff_mono {u v : A → B → ℝ} (h : ∀ a b, u a b ≤ v a b)
    (x : MixedStrategy A) (y : MixedStrategy B) : expPayoff u x y ≤ expPayoff v x y := by
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left (h a b) (mul_nonneg (x.nonneg a) (y.nonneg b))

public theorem le_expPayoff (u : A → B → ℝ) (x : MixedStrategy A) (y : MixedStrategy B)
    {L : ℝ} (h : ∀ a b, L ≤ u a b) : L ≤ expPayoff u x y := by
  simpa using expPayoff_mono h x y

public theorem expPayoff_le (u : A → B → ℝ) (x : MixedStrategy A) (y : MixedStrategy B)
    {U : ℝ} (h : ∀ a b, u a b ≤ U) : expPayoff u x y ≤ U := by
  simpa using expPayoff_mono h x y

/-- A finite, explicit bound, independent of the mixed strategies. -/
@[expose] public noncomputable def payoffBound (u : A → B → ℝ) : ℝ := ∑ a, ∑ b, |u a b|

omit [Nonempty A] [Nonempty B] in
public theorem abs_payoff_le_bound (u : A → B → ℝ) (a : A) (b : B) :
    |u a b| ≤ payoffBound u := by
  apply le_trans (Finset.single_le_sum (fun b' _ => abs_nonneg (u a b')) (Finset.mem_univ b))
  exact Finset.single_le_sum
    (fun a' _ => Finset.sum_nonneg (fun b' _ => abs_nonneg (u a' b'))) (Finset.mem_univ a)

public theorem expPayoff_bounds (u : A → B → ℝ) (x : MixedStrategy A) (y : MixedStrategy B) :
    -payoffBound u ≤ expPayoff u x y ∧ expPayoff u x y ≤ payoffBound u := by
  constructor
  · apply le_expPayoff
    intro a b
    exact (neg_le_neg (abs_payoff_le_bound u a b)).trans (neg_abs_le (u a b))
  · apply expPayoff_le
    intro a b
    exact (le_abs_self (u a b)).trans (abs_payoff_le_bound u a b)

public theorem expPayoff_bounded (u : A → B → ℝ) :
    ∃ L U : ℝ, ∀ x : MixedStrategy A, ∀ y : MixedStrategy B,
      L ≤ expPayoff u x y ∧ expPayoff u x y ≤ U :=
  ⟨-payoffBound u, payoffBound u, expPayoff_bounds u⟩

public theorem bddBelow_payoff_right (u : A → B → ℝ) (x : MixedStrategy A) :
    BddBelow (Set.range fun y : MixedStrategy B => expPayoff u x y) :=
  ⟨-payoffBound u, by rintro _ ⟨y, rfl⟩; exact (expPayoff_bounds u x y).1⟩

public theorem bddAbove_payoff_right (u : A → B → ℝ) (x : MixedStrategy A) :
    BddAbove (Set.range fun y : MixedStrategy B => expPayoff u x y) :=
  ⟨payoffBound u, by rintro _ ⟨y, rfl⟩; exact (expPayoff_bounds u x y).2⟩

public theorem bddBelow_payoff_left (u : A → B → ℝ) (y : MixedStrategy B) :
    BddBelow (Set.range fun x : MixedStrategy A => expPayoff u x y) :=
  ⟨-payoffBound u, by rintro _ ⟨x, rfl⟩; exact (expPayoff_bounds u x y).1⟩

public theorem bddAbove_payoff_left (u : A → B → ℝ) (y : MixedStrategy B) :
    BddAbove (Set.range fun x : MixedStrategy A => expPayoff u x y) :=
  ⟨payoffBound u, by rintro _ ⟨x, rfl⟩; exact (expPayoff_bounds u x y).2⟩

public theorem iInf_payoff_bounds (u : A → B → ℝ) (x : MixedStrategy A) :
    -payoffBound u ≤ (⨅ y : MixedStrategy B, expPayoff u x y) ∧
      (⨅ y : MixedStrategy B, expPayoff u x y) ≤ payoffBound u := by
  constructor
  · exact le_ciInf (fun y => (expPayoff_bounds u x y).1)
  · exact (ciInf_le (bddBelow_payoff_right u x) MixedStrategy.uniform).trans
      (expPayoff_bounds u x MixedStrategy.uniform).2

public theorem iSup_payoff_bounds (u : A → B → ℝ) (y : MixedStrategy B) :
    -payoffBound u ≤ (⨆ x : MixedStrategy A, expPayoff u x y) ∧
      (⨆ x : MixedStrategy A, expPayoff u x y) ≤ payoffBound u := by
  constructor
  · exact (expPayoff_bounds u MixedStrategy.uniform y).1.trans
      (le_ciSup (bddAbove_payoff_left u y) MixedStrategy.uniform)
  · exact ciSup_le (fun x => (expPayoff_bounds u x y).2)

public theorem bddAbove_iInf_payoff (u : A → B → ℝ) :
    BddAbove (Set.range fun x : MixedStrategy A => ⨅ y : MixedStrategy B, expPayoff u x y) :=
  ⟨payoffBound u, by rintro _ ⟨x, rfl⟩; exact (iInf_payoff_bounds u x).2⟩

public theorem bddBelow_iSup_payoff (u : A → B → ℝ) :
    BddBelow (Set.range fun y : MixedStrategy B => ⨆ x : MixedStrategy A, expPayoff u x y) :=
  ⟨-payoffBound u, by rintro _ ⟨y, rfl⟩; exact (iSup_payoff_bounds u y).1⟩

public theorem bddBelow_iInf_payoff (u : A → B → ℝ) :
    BddBelow (Set.range fun x : MixedStrategy A => ⨅ y : MixedStrategy B, expPayoff u x y) :=
  ⟨-payoffBound u, by rintro _ ⟨x, rfl⟩; exact (iInf_payoff_bounds u x).1⟩

public theorem bddAbove_iSup_payoff (u : A → B → ℝ) :
    BddAbove (Set.range fun y : MixedStrategy B => ⨆ x : MixedStrategy A, expPayoff u x y) :=
  ⟨payoffBound u, by rintro _ ⟨y, rfl⟩; exact (iSup_payoff_bounds u y).2⟩

/-- The maximizing player's guaranteed payoff. -/
@[expose] public noncomputable def maxminValue (u : A → B → ℝ) : ℝ :=
  ⨆ x : MixedStrategy A, ⨅ y : MixedStrategy B, expPayoff u x y

/-- The minimizing player's guaranteed payoff ceiling. -/
@[expose] public noncomputable def minmaxValue (u : A → B → ℝ) : ℝ :=
  ⨅ y : MixedStrategy B, ⨆ x : MixedStrategy A, expPayoff u x y

public theorem maxminValue_bounds (u : A → B → ℝ) :
    -payoffBound u ≤ maxminValue u ∧ maxminValue u ≤ payoffBound u := by
  constructor
  · exact (iInf_payoff_bounds u MixedStrategy.uniform).1.trans
      (le_ciSup (bddAbove_iInf_payoff u) MixedStrategy.uniform)
  · exact ciSup_le (fun x => (iInf_payoff_bounds u x).2)

public theorem minmaxValue_bounds (u : A → B → ℝ) :
    -payoffBound u ≤ minmaxValue u ∧ minmaxValue u ≤ payoffBound u := by
  constructor
  · exact le_ciInf (fun y => (iSup_payoff_bounds u y).1)
  · exact (ciInf_le (bddBelow_iSup_payoff u) MixedStrategy.uniform).trans
      (iSup_payoff_bounds u MixedStrategy.uniform).2

end Minimax
