import Mathlib

/-!
# Recovering a bounded slope from parallel strips

The final geometric step of paper Lemma 7.5: a first-coordinate interval cap rules out
nearly vertical strips of positive mass. The statements use finite probability laws, so they
apply to the original retained edges without changing their identities.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- A finite union bound, with nonnegative real weights. -/
theorem weighted_cover {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (P : ι → Prop)
    [DecidablePred P] {J : Type*} (s : Finset J) (Q : J → ι → Prop)
    [∀ j, DecidablePred (Q j)] (hcov : ∀ i, P i → ∃ j ∈ s, Q j i) :
    (∑ i, u i * (if P i then 1 else 0)) ≤
      ∑ j ∈ s, ∑ i, u i * (if Q j i then 1 else 0) := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : P i
  · obtain ⟨j, hj, hji⟩ := hcov i hi
    calc u i * (if P i then (1 : ℝ) else 0) = u i * (if Q j i then 1 else 0) := by
          rw [ite_eq_left hi, ite_eq_left hji]
      _ ≤ ∑ j ∈ s, u i * (if Q j i then 1 else 0) :=
          Finset.single_le_sum (f := fun j => u i * (if Q j i then 1 else 0))
            (fun j _ => mul_nonneg (hu i) (by split_ifs <;> norm_num)) hj
  · rw [ite_eq_right hi, mul_zero]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hu i) (by split_ifs <;> norm_num)

/-- A cap on half-open mesh intervals extends to all centered closed intervals. -/
theorem interval_cap_of_mesh {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (a : ι → ℝ)
    {h C : ℝ} (hh : 0 < h) (hC : 0 ≤ C)
    (hcap : ∀ x, (∑ i, u i * (if a i ∈ Set.Ico x (x + h) then 1 else 0)) ≤ C * h)
    (x r : ℝ) (hr : 0 ≤ r) :
    (∑ i, u i * (if |a i - x| ≤ r then 1 else 0)) ≤ 2 * C * (r + h) := by
  classical
  let N := ⌊2 * r / h⌋₊ + 1
  have hcov : ∀ i, |a i - x| ≤ r → ∃ j ∈ Finset.range N,
      a i ∈ Set.Ico (x - r + j * h) (x - r + j * h + h) := by
    intro i hi
    rw [abs_le] at hi
    have h0 : 0 ≤ (a i - (x - r)) / h := div_nonneg (by linarith) hh.le
    refine ⟨⌊(a i - (x - r)) / h⌋₊, ?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      apply Nat.floor_mono
      exact div_le_div_of_nonneg_right (by linarith) hh.le
    · have hlow := Nat.floor_le h0
      have hupp := Nat.lt_floor_add_one ((a i - (x - r)) / h)
      rw [le_div_iff₀ hh] at hlow
      rw [div_lt_iff₀ hh] at hupp
      constructor <;> nlinarith
  have hN : (N : ℝ) * h ≤ 2 * r + h := by
    have hfloor := Nat.floor_le (div_nonneg (by linarith : 0 ≤ 2 * r) hh.le)
    rw [le_div_iff₀ hh] at hfloor
    dsimp [N]
    push_cast
    nlinarith
  calc (∑ i, u i * (if |a i - x| ≤ r then (1 : ℝ) else 0))
      ≤ ∑ j ∈ Finset.range N, ∑ i, u i *
          (if a i ∈ Set.Ico (x - r + j * h) (x - r + j * h + h) then 1 else 0) :=
        weighted_cover hu _ _ _ hcov
    _ ≤ ∑ _j ∈ Finset.range N, C * h := Finset.sum_le_sum fun j _ => hcap _
    _ = C * ((N : ℝ) * h) := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ C * (2 * r + h) := mul_le_mul_of_nonneg_left hN hC
    _ ≤ 2 * C * (r + h) := by nlinarith

/-- Summing a rectangle cap over the possible second coordinates gives a marginal cap. -/
theorem marginal_cap_of_rectangle {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (a b : ι → ℝ)
    {h L : ℝ} (hh : 0 < h) (T : Finset ℝ) (hb : ∀ i, b i ∈ T)
    (hcap : ∀ x y, (∑ i, u i *
      (if a i ∈ Set.Ico x (x + h) ∧ b i ∈ Set.Ico y (y + h) then 1 else 0)) ≤ L)
    (x : ℝ) :
    (∑ i, u i * (if a i ∈ Set.Ico x (x + h) then 1 else 0)) ≤ T.card * L := by
  classical
  calc (∑ i, u i * (if a i ∈ Set.Ico x (x + h) then (1 : ℝ) else 0))
      ≤ ∑ y ∈ T, ∑ i, u i *
          (if a i ∈ Set.Ico x (x + h) ∧ b i ∈ Set.Ico y (y + h) then 1 else 0) := by
        apply weighted_cover hu
        intro i hi
        exact ⟨b i, hb i, hi, le_rfl, by linarith⟩
    _ ≤ ∑ _y ∈ T, L := Finset.sum_le_sum fun y _ => hcap x y
    _ = T.card * L := by simp

/-- A marginal interval cap bounds the probability that two independent first endpoints are close. -/
theorem short_pair_mass_le {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (hu1 : ∑ i, u i = 1)
    (a : ι → ℝ × ℝ) {h C : ℝ}
    (hcap : ∀ x r, 0 ≤ r →
      (∑ i, u i * (if |(a i).1 - x| ≤ r then 1 else 0)) ≤ C * (r + h))
    (q : ℝ) (hq : 0 ≤ q) :
    (∑ p : ι × ι, u p.1 * u p.2 *
      (if max |(a p.1 - a p.2).1| |(a p.1 - a p.2).2| < q then 1 else 0)) ≤ C * (q + h) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc (∑ j, ∑ i, u i * u j *
        (if max |(a i - a j).1| |(a i - a j).2| < q then (1 : ℝ) else 0))
      ≤ ∑ j, u j * ∑ i, u i * (if |(a i).1 - (a j).1| ≤ q then 1 else 0) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        have hind : (if max |(a i - a j).1| |(a i - a j).2| < q then (1 : ℝ) else 0) ≤
            (if |(a i).1 - (a j).1| ≤ q then 1 else 0) := by
          split_ifs with hshort hclose hclose
          · exact le_rfl
          · exact False.elim (hclose ((le_max_left _ _).trans hshort.le))
          · norm_num
          · exact le_rfl
        calc _ ≤ u i * u j * (if |(a i).1 - (a j).1| ≤ q then (1 : ℝ) else 0) :=
              mul_le_mul_of_nonneg_left hind (mul_nonneg (hu i) (hu j))
          _ = _ := by ring
    _ ≤ ∑ j, u j * (C * (q + h)) := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hcap _ q hq) (hu j)
    _ = C * (q + h) := by rw [← Finset.sum_mul, hu1, one_mul]

/-- A positive-mass strip cannot have an arbitrarily small horizontal direction component. -/
theorem strip_horizontal_lower {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (a : ι → ℝ × ℝ)
    (P : ι → Prop) [DecidablePred P] {h C D p q Δ : ℝ}
    (hh : 0 ≤ h) (hC : 1 ≤ C) (hD : 1 ≤ D) (hp : 0 < p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hΔ : 0 ≤ Δ)
    (hcap : ∀ x r, 0 ≤ r →
      (∑ i, u i * (if |(a i).1 - x| ≤ r then 1 else 0)) ≤ C * (r + h))
    (hbound : ∀ i, |(a i).2| ≤ D)
    (hmass : p ≤ ∑ i, u i * (if P i then 1 else 0))
    (v x₀ : ℝ × ℝ) (hv : q ≤ max |v.1| |v.2|)
    (hstrip : ∀ i, P i →
      |((a i).1 - x₀.1) * v.2 - ((a i).2 - x₀.2) * v.1| ≤ Δ)
    (hsmall : 4 * C * (Δ / q + h) ≤ p) :
    p * q / (4 * C * D) ≤ |v.1| := by
  classical
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hCD : 1 ≤ C * D := by nlinarith
  have hden : 0 < 4 * C * D := by positivity
  by_cases hv₁ : q ≤ |v.1|
  · apply le_trans ?_ hv₁
    rw [div_le_iff₀ hden]
    nlinarith
  have hv₂ : q ≤ |v.2| := by
    rw [le_max_iff] at hv
    exact hv.resolve_left hv₁
  have hv₂0 : 0 < |v.2| := lt_of_lt_of_le hq hv₂
  obtain ⟨i₀, hi₀⟩ : ∃ i, P i := by
    by_contra! hn
    have hz : (∑ i, u i * (if P i then (1 : ℝ) else 0)) = 0 := by simp [hn]
    linarith
  let r := (2 * Δ + 2 * D * |v.1|) / |v.2|
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hclose : ∀ i, P i → |(a i).1 - (a i₀).1| ≤ r := by
    intro i hi
    have hw : |((a i).1 - (a i₀).1) * v.2 - ((a i).2 - (a i₀).2) * v.1| ≤ 2 * Δ := by
      have heq : ((a i).1 - (a i₀).1) * v.2 - ((a i).2 - (a i₀).2) * v.1 =
          (((a i).1 - x₀.1) * v.2 - ((a i).2 - x₀.2) * v.1) -
          (((a i₀).1 - x₀.1) * v.2 - ((a i₀).2 - x₀.2) * v.1) := by ring
      rw [heq]
      exact (abs_sub _ _).trans (by linarith [hstrip i hi, hstrip i₀ hi₀])
    have hsecond : |(a i).2 - (a i₀).2| ≤ 2 * D :=
      (abs_sub _ _).trans (by linarith [hbound i, hbound i₀])
    have hfirst : |((a i).1 - (a i₀).1) * v.2| ≤ 2 * Δ + 2 * D * |v.1| := by
      calc |((a i).1 - (a i₀).1) * v.2|
          = |(((a i).1 - (a i₀).1) * v.2 - ((a i).2 - (a i₀).2) * v.1) +
              ((a i).2 - (a i₀).2) * v.1| := by congr 1; ring
        _ ≤ |((a i).1 - (a i₀).1) * v.2 - ((a i).2 - (a i₀).2) * v.1| +
              |((a i).2 - (a i₀).2) * v.1| := abs_add_le _ _
        _ ≤ 2 * Δ + 2 * D * |v.1| := by rw [abs_mul]; gcongr
    dsimp [r]
    rw [le_div_iff₀ hv₂0, ← abs_mul]
    exact hfirst
  have hmass' : p ≤ C * (r + h) := by
    calc p ≤ ∑ i, u i * (if P i then (1 : ℝ) else 0) := hmass
      _ ≤ ∑ i, u i * (if |(a i).1 - (a i₀).1| ≤ r then 1 else 0) := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hu i)
          by_cases hi : P i
          · rw [ite_eq_left hi, ite_eq_left (hclose i hi)]
          · rw [ite_eq_right hi]; split_ifs <;> norm_num
      _ ≤ C * (r + h) := hcap _ _ hr
  have hrle : r ≤ (2 * Δ + 2 * D * |v.1|) / q :=
    div_le_div_of_nonneg_left (by positivity) hq hv₂
  have hmass'' : p ≤ C * ((2 * Δ + 2 * D * |v.1|) / q + h) := by
    exact hmass'.trans (mul_le_mul_of_nonneg_left (by linarith :
      r + h ≤ (2 * Δ + 2 * D * |v.1|) / q + h) hC0.le)
  have hsmall' : 4 * C * (Δ + h * q) ≤ p * q := by
    have heq : (Δ / q + h) * q = Δ + h * q := by field_simp
    have hs := mul_le_mul_of_nonneg_right hsmall hq.le
    nlinarith [heq]
  have hmass''' : p * q ≤ C * (2 * Δ + 2 * D * |v.1| + h * q) := by
    have heq : ((2 * Δ + 2 * D * |v.1|) / q + h) * q =
        2 * Δ + 2 * D * |v.1| + h * q := by field_simp
    have hs := mul_le_mul_of_nonneg_right hmass'' hq.le
    nlinarith [heq]
  rw [div_le_iff₀ hden]
  nlinarith [mul_nonneg hC0.le (mul_nonneg hh hq.le)]

/-- Translating a wedge strip to a line through one occupied endpoint costs a factor two. -/
theorem line_error_of_wedge {x x' x₀ v : ℝ × ℝ} {Δ : ℝ} (hv : v.1 ≠ 0)
    (hx : |(x.1 - x₀.1) * v.2 - (x.2 - x₀.2) * v.1| ≤ Δ)
    (hx' : |(x'.1 - x₀.1) * v.2 - (x'.2 - x₀.2) * v.1| ≤ Δ) :
    |x.2 - (v.2 / v.1) * x.1 - (x'.2 - (v.2 / v.1) * x'.1)| ≤ 2 * Δ / |v.1| := by
  have heq : x.2 - (v.2 / v.1) * x.1 - (x'.2 - (v.2 / v.1) * x'.1) =
      -(((x.1 - x₀.1) * v.2 - (x.2 - x₀.2) * v.1) -
        ((x'.1 - x₀.1) * v.2 - (x'.2 - x₀.2) * v.1)) / v.1 := by field_simp; ring
  rw [heq, abs_div, abs_neg]
  exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (by linarith)) (abs_nonneg _)

/-- Positive mass in parallel wedge strips yields a common bounded slope and bounded intercepts.
The same indices satisfy the resulting line estimates. -/
theorem parallel_strip_fit {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (a b : ι → ℝ × ℝ)
    (P : ι → Prop) [DecidablePred P] {h C D p q Δ : ℝ}
    (hh : 0 ≤ h) (hC : 1 ≤ C) (hD : 1 ≤ D) (hp : 0 < p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hΔ : 0 ≤ Δ)
    (hcap : ∀ x r, 0 ≤ r →
      (∑ i, u i * (if |(a i).1 - x| ≤ r then 1 else 0)) ≤ C * (r + h))
    (ha : ∀ i, |(a i).1| ≤ D ∧ |(a i).2| ≤ D)
    (hb : ∀ i, |(b i).1| ≤ D ∧ |(b i).2| ≤ D)
    (hmass : p ≤ ∑ i, u i * (if P i then 1 else 0))
    (v x₀ y₀ : ℝ × ℝ) (hv : q ≤ max |v.1| |v.2|)
    (hstrip : ∀ i, P i →
      |((a i).1 - x₀.1) * v.2 - ((a i).2 - x₀.2) * v.1| ≤ Δ ∧
      |((b i).1 - y₀.1) * v.2 - ((b i).2 - y₀.2) * v.1| ≤ Δ)
    (hsmall : 4 * C * (Δ / q + h) ≤ p) :
    ∃ ℓ c₁ c₂ : ℝ,
      |ℓ| + |c₁| + |c₂| ≤ (1 + 2 * D) * (4 * C * D / p) + 2 * D ∧
      ∀ i, P i → |(a i).2 - ℓ * (a i).1 - c₁| +
        |(b i).2 - ℓ * (b i).1 - c₂| ≤ 16 * C * D * Δ / (p * q) := by
  classical
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hden : 0 < 4 * C * D := by positivity
  have hmax : 0 < max |v.1| |v.2| := lt_of_lt_of_le hq hv
  have hsmall' : 4 * C * (Δ / max |v.1| |v.2| + h) ≤ p := by
    refine le_trans ?_ hsmall
    exact mul_le_mul_of_nonneg_left
      (by linarith [div_le_div_of_nonneg_left hΔ hq hv]) (by positivity)
  have hhorizontal := strip_horizontal_lower hu a P hh hC hD hp hp1 hmax hΔ hcap
    (fun i => (ha i).2) hmass v x₀ le_rfl (fun i hi => (hstrip i hi).1) hsmall'
  have hv₁0 : 0 < |v.1| := lt_of_lt_of_le (by positivity) hhorizontal
  have hv₁ : v.1 ≠ 0 := abs_pos.mp hv₁0
  have hhorizontal' : p * max |v.1| |v.2| ≤ |v.1| * (4 * C * D) :=
    (div_le_iff₀ hden).mp hhorizontal
  have hslope : |v.2 / v.1| ≤ 4 * C * D / p := by
    rw [abs_div, div_le_div_iff₀ hv₁0 hp]
    nlinarith [mul_le_mul_of_nonneg_left (le_max_right |v.1| |v.2|) hp.le]
  have herror : 4 * Δ / |v.1| ≤ 16 * C * D * Δ / (p * q) := by
    rw [div_le_div_iff₀ hv₁0 (mul_pos hp hq)]
    have hhor : p * q ≤ |v.1| * (4 * C * D) := by
      exact (mul_le_mul_of_nonneg_left hv hp.le).trans hhorizontal'
    nlinarith [mul_le_mul_of_nonneg_right hhor hΔ]
  obtain ⟨i₀, hi₀⟩ : ∃ i, P i := by
    by_contra! hn
    have hz : (∑ i, u i * (if P i then (1 : ℝ) else 0)) = 0 := by simp [hn]
    linarith
  refine ⟨v.2 / v.1, (a i₀).2 - (v.2 / v.1) * (a i₀).1,
    (b i₀).2 - (v.2 / v.1) * (b i₀).1, ?_, ?_⟩
  · have hca : |(a i₀).2 - (v.2 / v.1) * (a i₀).1| ≤ D + |v.2 / v.1| * D := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul]
      gcongr
      · exact (ha i₀).2
      · exact (ha i₀).1
    have hcb : |(b i₀).2 - (v.2 / v.1) * (b i₀).1| ≤ D + |v.2 / v.1| * D := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul]
      gcongr
      · exact (hb i₀).2
      · exact (hb i₀).1
    nlinarith [mul_le_mul_of_nonneg_right hslope hD0.le]
  · intro i hi
    have h₁ := line_error_of_wedge hv₁ (hstrip i hi).1 (hstrip i₀ hi₀).1
    have h₂ := line_error_of_wedge hv₁ (hstrip i hi).2 (hstrip i₀ hi₀).2
    have hsum : |(a i).2 - (v.2 / v.1) * (a i).1 -
          ((a i₀).2 - (v.2 / v.1) * (a i₀).1)| +
        |(b i).2 - (v.2 / v.1) * (b i).1 -
          ((b i₀).2 - (v.2 / v.1) * (b i₀).1)| ≤ 4 * Δ / |v.1| := by
      calc _ ≤ 2 * Δ / |v.1| + 2 * Δ / |v.1| := add_le_add h₁ h₂
        _ = 4 * Δ / |v.1| := by ring
    exact hsum.trans herror

omit [Fintype ι] in
/-- Undoing a nonzero dilation of the second endpoint preserves the common slope. -/
theorem unscale_parallel_fit (a b : ι → ℝ × ℝ) (P : ι → Prop)
    {κ ℓ c₁ c₂ K L E : ℝ} (hK : 1 ≤ K) (hκ : κ ≠ 0) (hκinv : |κ⁻¹| ≤ K)
    (hcoeff : |ℓ| + |c₁| + |c₂| ≤ L)
    (hfit : ∀ i, P i → |(a i).2 - ℓ * (a i).1 - c₁| +
      |κ * (b i).2 - ℓ * (κ * (b i).1) - c₂| ≤ E) :
    |ℓ| + |c₁| + |c₂ / κ| ≤ K * L ∧
      ∀ i, P i → |(a i).2 - ℓ * (a i).1 - c₁| +
        |(b i).2 - ℓ * (b i).1 - c₂ / κ| ≤ K * E := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hdiv : ∀ z : ℝ, |z / κ| ≤ K * |z| := by
    intro z
    rw [abs_div, div_eq_mul_inv, ← abs_inv]
    exact (mul_le_mul_of_nonneg_left hκinv (abs_nonneg z)).trans_eq (mul_comm _ _)
  constructor
  · have hl : |ℓ| ≤ K * |ℓ| := by nlinarith [abs_nonneg ℓ]
    have hc : |c₁| ≤ K * |c₁| := by nlinarith [abs_nonneg c₁]
    have hc₂ := hdiv c₂
    nlinarith [mul_le_mul_of_nonneg_left hcoeff hK0]
  · intro i hi
    have heq : (b i).2 - ℓ * (b i).1 - c₂ / κ =
        (κ * (b i).2 - ℓ * (κ * (b i).1) - c₂) / κ := by field_simp
    rw [heq]
    have hfirst : |(a i).2 - ℓ * (a i).1 - c₁| ≤ K * |(a i).2 - ℓ * (a i).1 - c₁| := by
      nlinarith [abs_nonneg ((a i).2 - ℓ * (a i).1 - c₁)]
    have hsecond := hdiv (κ * (b i).2 - ℓ * (κ * (b i).1) - c₂)
    nlinarith [mul_le_mul_of_nonneg_left (hfit i hi) hK0]

end

end Submission.Obl.k4_retained_edge_planar_rigidity
