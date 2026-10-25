import Mathlib
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.Packets
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.QuadBounds
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds

/-!
# From true terminal chart systems to the frozen packet output

A version-1 true terminal chart system (paper Definition 2.8 with the test `w - F(t, y)`)
has, on a common dyadic block of length `q = 2^{-T}`, disjoint trajectory assignments, an
affine spatial centre `c₀ + c₁ t`, a spatial width `J ≤ Λ q`, spatial confinement
`|y - (c₀ + c₁ t)| ≤ Λ J`, the fit `|x - F(t, y)| ≤ Λ N^{-L}` and the true floor
`μ(A × I) ≥ N^{-f(L)} J q / Λ`, with total mass at least `Λ⁻¹`.

This file converts such a system into the frozen output `HasPackets`: narrow packets carry
mostly exceptional angular density and thin packets mostly exceptional pure density, so both
can be discarded in aggregate; the remaining packets have spatial width comparable to `q` up to
the allowed losses, and the Remez inequality on their parallelogram bounds the predictor on
the block times `[-1, 1]`.
-/

namespace Submission.Obl.k4_scalar_terminal_chart_packet_extraction

open MeasureTheory Set
open scoped ENNReal

/-- A version-1 true terminal chart system at one sample, with slack `Λ` and time cost
`2^T ≤ N^h` (paper Definition 2.8). -/
def HasTrueSystem (N : ℝ) (W : ℕ) (ω : Fin W → ℝ) (μ : Fin W → Measure (Coeff × ℝ))
    (L fL h Λ : ℝ) : Prop :=
  ∃ (T n : ℕ) (γ : Fin n → Fin W) (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set Coeff)
      (F : Fin n → MvPolynomial (Fin 2) ℝ) (c₀ c₁ J : Fin n → ℝ),
    (2 : ℝ) ^ T ≤ N ^ h ∧
    (∀ i, MeasurableSet (A i)) ∧
    (∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i')) ∧
    (∀ i, (F i).totalDegree ≤ 2 ∧ 0 < J i ∧ J i ≤ Λ / 2 ^ T ∧
      (∀ l ∈ A i, ∀ t ∈ block T (j i),
        |spatial l t - (c₀ i + c₁ i * t)| ≤ Λ * J i ∧
        |hidden l t - MvPolynomial.eval ![t, spatial l t] (F i)| ≤ Λ * N ^ (-L)) ∧
      ENNReal.ofReal (N ^ (-fL) * J i / (Λ * 2 ^ T)) ≤ μ (γ i) (A i ×ˢ block T (j i))) ∧
    ENNReal.ofReal Λ⁻¹ ≤ ∑ g : Fin W, ENNReal.ofReal (ω g) *
      μ g {p | ∃ i, γ i = g ∧ p.1 ∈ A i ∧ p.2 ∈ block T (j i)}

/-! ### Dyadic blocks -/

lemma block_eq (T : ℕ) (j : Fin (2 ^ T)) :
    block T j = Icc ((j : ℕ) / (2 : ℝ) ^ T) ((j : ℕ) / (2 : ℝ) ^ T + 1 / (2 : ℝ) ^ T) := by
  unfold block; rw [add_div]

lemma block_subset_unit (T : ℕ) (j : Fin (2 ^ T)) : block T j ⊆ Icc 0 1 := by
  intro t ht
  unfold block at ht
  have h2 : (0 : ℝ) < 2 ^ T := by positivity
  have hj : ((j : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ T := by
    have := j.isLt
    exact_mod_cast this
  constructor
  · exact le_trans (by positivity) ht.1
  · exact ht.2.trans ((div_le_one h2).mpr hj)

lemma block_inter_subset (T : ℕ) {j j' : Fin (2 ^ T)} (hjj : j < j') :
    block T j ∩ block T j' ⊆ {((j' : ℕ) : ℝ) / (2 : ℝ) ^ T} := by
  intro t ⟨h1, h2⟩
  unfold block at h1 h2
  have h2T : (0 : ℝ) < 2 ^ T := by positivity
  have hle : ((j : ℕ) : ℝ) + 1 ≤ ((j' : ℕ) : ℝ) := by
    have : (j : ℕ) + 1 ≤ (j' : ℕ) := hjj
    exact_mod_cast this
  have : (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T ≤ ((j' : ℕ) : ℝ) / (2 : ℝ) ^ T :=
    div_le_div_of_nonneg_right hle h2T.le
  exact le_antisymm (by linarith [h1.2]) h2.1

lemma measure_blocks_inter_zero {μ : Measure (Coeff × ℝ)}
    (hpt : ∀ t, μ (univ ×ˢ {t}) = 0) (T : ℕ) {j j' : Fin (2 ^ T)} (hjj : j ≠ j')
    (S S' : Set Coeff) : μ ((S ×ˢ block T j) ∩ (S' ×ˢ block T j')) = 0 := by
  rcases lt_or_gt_of_ne hjj with h | h
  · refine measure_mono_null ?_ (hpt (((j' : ℕ) : ℝ) / (2 : ℝ) ^ T))
    rintro ⟨l, t⟩ ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩
    exact ⟨trivial, block_inter_subset T h ⟨ht, ht'⟩⟩
  · refine measure_mono_null ?_ (hpt (((j : ℕ) : ℝ) / (2 : ℝ) ^ T))
    rintro ⟨l, t⟩ ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩
    exact ⟨trivial, block_inter_subset T h ⟨ht', ht⟩⟩

/-! ### The single-sample conversion -/

/-- **Single-sample conversion.** A true terminal system yields the frozen packet output,
once the explicit parameter inequalities `P1`--`P6` hold. `θG`, `θL` are the angular and pure
density thresholds whose exceedance sets are discarded, `b` is the velocity bin width and
`lam` the Remez density fraction. -/
theorem packets_of_trueSystem {W : ℕ} {ω : Fin W → ℝ} {μ : Fin W → Measure (Coeff × ℝ)}
    {N L fL h ε Λ K b θL θG lam : ℝ}
    (hN : 0 < N) (hΛ : 1 ≤ Λ) (hK : 0 ≤ K) (hb : 0 < b) (hθL : 0 ≤ θL) (hθG : 0 ≤ θG)
    (hlam : 0 < lam)
    (hcoef : ∀ g, μ g {p | ∃ e, K < |p.1.2 e|} = 0)
    (hpt : ∀ g t, μ g (univ ×ˢ {t}) = 0)
    (hfin : ∀ g, μ g univ ≠ ⊤)
    (gL : Fin W → (Fin 2 → ℝ) × ℤ → ℝ≥0∞) (hgL : ∀ g, Measurable (gL g))
    (hmapL : ∀ g, Measure.map (obsL (N ^ (-L))) (μ g) =
      (volume.prod Measure.count).withDensity (gL g))
    (GG : Fin W → ((Fin 2 → ℝ) × ℤ) × ℤ → ℝ≥0∞) (hGG : ∀ g, Measurable (GG g))
    (hmapG : ∀ g, Measure.map (obsG (N ^ (-L)) b) (μ g) =
      ((volume.prod Measure.count).prod Measure.count).withDensity (GG g))
    (P1 : 16 * Λ ^ 2 * (2 * Λ + 3) * θG ≤ N ^ (-fL))
    (P2 : 4 * Λ ^ 2 * N ^ (-ε) ≤ b * N ^ (-h))
    (P3 : 4 * Λ ^ 2 * (2 * Λ + 3) * lam * θL ≤ N ^ (-fL))
    (P4 : 186624 * (3 * K + Λ * N ^ (-L)) * (4 + (1 + 2 * K) * (4 * N ^ h / b)) ^ 2 / lam ^ 4
      ≤ N ^ ε)
    (P5 : ENNReal.ofReal (N ^ (-ε)) +
      (2 * ∑ g, ENNReal.ofReal (ω g) *
          μ g {p | ENNReal.ofReal θG < GG g (obsG (N ^ (-L)) b p)} +
        2 * ∑ g, ENNReal.ofReal (ω g) *
          μ g {p | ENNReal.ofReal θL < gL g (obsL (N ^ (-L)) p)}) ≤ ENNReal.ofReal Λ⁻¹)
    (P6 : Λ ≤ N ^ ε)
    (hsys : HasTrueSystem N W ω μ L fL h Λ) :
    HasPackets N W ω μ L fL h ε := by
  classical
  obtain ⟨T, n, γ, j, A, F, c₀, c₁, J, hT, hAm, hdisj, hpk, hmass⟩ := hsys
  set a := N ^ (-L) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hN _
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  have h2T : (0 : ℝ) < 2 ^ T := by positivity
  set q : ℝ := 1 / (2 : ℝ) ^ T with hq_def
  have hq : 0 < q := by positivity
  have hNh : 0 < N ^ h := Real.rpow_pos_of_pos hN _
  have hqh : N ^ (-h) ≤ q := by
    rw [hq_def, Real.rpow_neg hN.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le h2T hT
  set st : Fin n → ℝ := fun i => ((j i : ℕ) : ℝ) / (2 : ℝ) ^ T with hst
  have hblock : ∀ i, block T (j i) = Icc (st i) (st i + q) := fun i => by
    rw [block_eq]
  have hblock01 : ∀ i, ∀ t ∈ Icc (st i) (st i + q), t ∈ Icc (0 : ℝ) 1 := by
    intro i t ht
    rw [← hblock] at ht
    exact block_subset_unit T (j i) ht
  set Good : Set Coeff := {l | ∀ e, |l.2 e| ≤ K} with hGood
  have hGoodm : MeasurableSet Good := by
    have : Good = ⋂ e, {l : Coeff | |l.2 e| ≤ K} := by ext l; simp [hGood]
    rw [this]
    exact MeasurableSet.iInter (fun e => measurableSet_le (by fun_prop) measurable_const)
  set A' : Fin n → Set Coeff := fun i => A i ∩ Good with hA'
  have hA'm : ∀ i, MeasurableSet (A' i) := fun i => (hAm i).inter hGoodm
  set f : Fin n → ℝ → ℝ → ℝ := fun i t y => MvPolynomial.eval ![t, y] (F i) with hf
  have hfq : ∀ i, IsQuad2 (f i) := fun i => isQuad2_eval (F i) (hpk i).1
  set w : Fin n → ℝ := fun i => Λ * J i with hw
  have hw0 : ∀ i, 0 < w i := fun i => mul_pos hΛ0 (hpk i).2.1
  set A₀ : ℝ := 3 * K + Λ * a with hA₀
  set Z : Fin n → Set (ℝ × ℝ) := fun i => {p : ℝ × ℝ | p.1 ∈ Icc (st i) (st i + q) ∧
    |p.2 - (c₀ i + c₁ i * p.1)| ≤ w i ∧ |f i p.1 p.2| ≤ A₀} with hZ
  set Pk : Fin n → Set (Coeff × ℝ) := fun i => A' i ×ˢ Icc (st i) (st i + q) with hPk
  have hPkm : ∀ i, MeasurableSet (Pk i) := fun i => (hA'm i).prod measurableSet_Icc
  set XG : Fin W → Set (Coeff × ℝ) := fun g => {p | ENNReal.ofReal θG < GG g (obsG a b p)}
    with hXG
  set XL : Fin W → Set (Coeff × ℝ) := fun g => {p | ENNReal.ofReal θL < gL g (obsL a p)}
    with hXL
  have hXGm : ∀ g, MeasurableSet (XG g) := fun g =>
    measurableSet_lt measurable_const ((hGG g).comp (measurable_obsG a b))
  have hXLm : ∀ g, MeasurableSet (XL g) := fun g =>
    measurableSet_lt measurable_const ((hgL g).comp (measurable_obsL a))
  -- the coefficient-good part carries all the mass
  have hbadcoef : ∀ g, μ g {p : Coeff × ℝ | p.1 ∉ Good} = 0 := by
    intro g
    refine measure_mono_null ?_ (hcoef g)
    intro p hp
    simp only [hGood, Set.mem_ofPred_eq, not_forall, not_le] at hp
    exact hp
  have hK1 : ∀ i, μ (γ i) (A i ×ˢ block T (j i)) ≤ μ (γ i) (Pk i) := by
    intro i
    calc μ (γ i) (A i ×ˢ block T (j i))
        ≤ μ (γ i) (Pk i ∪ {p : Coeff × ℝ | p.1 ∉ Good}) := by
          apply measure_mono
          rintro ⟨l, t⟩ ⟨hl, ht⟩
          by_cases hg : l ∈ Good
          · left; exact ⟨⟨hl, hg⟩, by rw [← hblock]; exact ht⟩
          · right; exact hg
      _ ≤ μ (γ i) (Pk i) + μ (γ i) {p : Coeff × ℝ | p.1 ∉ Good} := measure_union_le _ _
      _ = μ (γ i) (Pk i) := by rw [hbadcoef, add_zero]
  -- floors in terms of `q`
  have hfloor : ∀ i, ENNReal.ofReal (N ^ (-fL) * J i * q / Λ) ≤ μ (γ i) (Pk i) := by
    intro i
    refine le_trans (le_of_eq ?_) (((hpk i).2.2.2.2).trans (hK1 i))
    congr 1
    rw [hq_def]
    field_simp
  have hNfL : 0 < N ^ (-fL) := Real.rpow_pos_of_pos hN _
  have hfloorpos : ∀ i, 0 < μ (γ i) (Pk i) := by
    intro i
    refine lt_of_lt_of_le ?_ (hfloor i)
    rw [ENNReal.ofReal_pos]
    have := (hpk i).2.1
    positivity
  -- confinement on the good part
  have hconf : ∀ i, ∀ l ∈ A' i, ∀ t ∈ Icc (st i) (st i + q),
      |spatial l t - (c₀ i + c₁ i * t)| ≤ w i ∧ |hidden l t - f i t (spatial l t)| ≤ Λ * a := by
    intro i l hl t ht
    rw [← hblock] at ht
    exact (hpk i).2.2.2.1 l hl.1 t ht
  have hval : ∀ i, ∀ l ∈ A' i, ∀ t ∈ Icc (st i) (st i + q), |f i t (spatial l t)| ≤ A₀ := by
    intro i l hl t ht
    have ht01 := hblock01 i t ht
    have hc := l
    have hb2 := hl.2 2
    have hb3 := hl.2 3
    have hb4 := hl.2 4
    have hhid : |hidden l t| ≤ 3 * K := by
      unfold hidden
      have e1 : |t * l.2 3| ≤ K := by
        rw [abs_mul, abs_of_nonneg ht01.1]
        calc t * |l.2 3| ≤ 1 * K := mul_le_mul ht01.2 hb3 (abs_nonneg _) zero_le_one
          _ = K := one_mul K
      have e2 : |t ^ 2 * l.2 4| ≤ K := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        have : t ^ 2 ≤ 1 := by nlinarith [ht01.1, ht01.2]
        calc t ^ 2 * |l.2 4| ≤ 1 * K := mul_le_mul this hb4 (abs_nonneg _) zero_le_one
          _ = K := one_mul K
      calc |l.2 2 + t * l.2 3 + t ^ 2 * l.2 4| ≤ |l.2 2| + |t * l.2 3| + |t ^ 2 * l.2 4| :=
            abs_add_three _ _ _
        _ ≤ 3 * K := by linarith
    have hfit := (hconf i l hl t ht).2
    calc |f i t (spatial l t)| = |hidden l t - (hidden l t - f i t (spatial l t))| := by ring_nf
      _ ≤ |hidden l t| + |hidden l t - f i t (spatial l t)| := abs_sub _ _
      _ ≤ A₀ := by rw [hA₀]; linarith
  -- classification of packets
  set narrowIdx : Finset (Fin n) := Finset.univ.filter (fun i => 4 * w i ≤ b * q) with hnarrowIdx
  set thinIdx : Finset (Fin n) := Finset.univ.filter (fun i => ¬ 4 * w i ≤ b * q ∧
    volume (Z i) < ENNReal.ofReal (lam * (q * (2 * w i)))) with hthinIdx
  set goodIdx : Finset (Fin n) := Finset.univ.filter (fun i => ¬ 4 * w i ≤ b * q ∧
    ENNReal.ofReal (lam * (q * (2 * w i))) ≤ volume (Z i)) with hgoodIdx
  -- narrow packets are mostly angularly exceptional
  have hnarrow : ∀ i ∈ narrowIdx, μ (γ i) (Pk i) ≤ 2 * μ (γ i) (Pk i ∩ XG (γ i)) := by
    intro i hi
    simp only [hnarrowIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hd := narrow_packet_diff_le (hGG (γ i)) ha hb (hmapG (γ i)) (hfq i) hq (hw0 i).le
      hΛ0.le (hconf i) hi (ENNReal.ofReal θG)
    refine le_two_mul_inter_of_diff_le _ (by finiteness) hd ?_
    refine le_trans ?_ (hfloor i)
    rw [← ENNReal.ofReal_mul hθG, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have hJ := (hpk i).2.1
    have key : 16 * Λ ^ 2 * (2 * Λ + 3) * θG * (J i * q) ≤ N ^ (-fL) * (J i * q) :=
      mul_le_mul_of_nonneg_right P1 (by positivity)
    rw [hw]
    rw [le_div_iff₀ hΛ0]
    nlinarith [key]
  -- thin packets are mostly exceptional for the pure density
  have hthin : ∀ i ∈ thinIdx, μ (γ i) (Pk i) ≤ 2 * μ (γ i) (Pk i ∩ XL (γ i)) := by
    intro i hi
    simp only [hthinIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hd := thin_packet_diff_le (hgL (γ i)) ha (hmapL (γ i)) (hfq i) hΛ0.le (hconf i)
      (hval i) (ENNReal.ofReal θL)
    have hZfin : volume (Z i) ≠ ⊤ := ne_top_of_lt hi.2
    refine le_two_mul_inter_of_diff_le _ (by finiteness) hd ?_
    refine le_trans ?_ (hfloor i)
    calc 2 * (ENNReal.ofReal θL * (ENNReal.ofReal (2 * Λ + 3) * volume (Z i)))
        ≤ 2 * (ENNReal.ofReal θL * (ENNReal.ofReal (2 * Λ + 3) *
            ENNReal.ofReal (lam * (q * (2 * w i))))) := by
          gcongr
          exact hi.2.le
      _ = ENNReal.ofReal (2 * (θL * ((2 * Λ + 3) * (lam * (q * (2 * w i)))))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hθL,
            ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      _ ≤ ENNReal.ofReal (N ^ (-fL) * J i * q / Λ) := by
          apply ENNReal.ofReal_le_ofReal
          have hJ := (hpk i).2.1
          have key : 4 * Λ ^ 2 * (2 * Λ + 3) * lam * θL * (J i * q) ≤ N ^ (-fL) * (J i * q) :=
            mul_le_mul_of_nonneg_right P3 (by positivity)
          rw [hw, le_div_iff₀ hΛ0]
          nlinarith [key]
  -- good packets are wide and saturate their parallelogram
  have hgood_wide : ∀ i ∈ goodIdx, b * q < 4 * w i := by
    intro i hi
    simp only [hgoodIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact lt_of_not_ge hi.1
  have hgood_vol : ∀ i ∈ goodIdx,
      ENNReal.ofReal (lam * (q * (2 * w i))) ≤ volume (Z i) := by
    intro i hi
    simp only [hgoodIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi.2
  have hNe : 0 < N ^ ε := Real.rpow_pos_of_pos hN _
  have hNmh : N ^ (-h) = (N ^ h)⁻¹ := Real.rpow_neg hN.le h
  have hNme : N ^ (-ε) = (N ^ ε)⁻¹ := Real.rpow_neg hN.le ε
  -- `b ≤ 4 w N^h` on good packets
  have hbw : ∀ i ∈ goodIdx, b ≤ 4 * w i * N ^ h := by
    intro i hi
    have h1 : b * N ^ (-h) < 4 * w i :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hqh hb.le) (hgood_wide i hi)
    rw [hNmh] at h1
    have h2 : b * (N ^ h)⁻¹ * N ^ h = b := by field_simp
    nlinarith [h1, hNh]
  have hgood_floor : ∀ i ∈ goodIdx,
      ENNReal.ofReal (N ^ (-fL) / (N ^ ε * (2 : ℝ) ^ T)) ≤ μ (γ i) (Pk i) := by
    intro i hi
    refine le_trans ?_ (hfloor i)
    apply ENNReal.ofReal_le_ofReal
    have h1 : b * N ^ (-h) ≤ b * q := mul_le_mul_of_nonneg_left hqh hb.le
    have hJ : Λ * N ^ (-ε) ≤ J i := by
      have : 4 * Λ ^ 2 * N ^ (-ε) < 4 * (Λ * J i) :=
        lt_of_le_of_lt (P2.trans h1) (hgood_wide i hi)
      nlinarith
    rw [hNme] at hJ
    have hJ' : (N ^ ε)⁻¹ ≤ J i / Λ := by rw [le_div_iff₀ hΛ0]; linarith [hJ]
    calc N ^ (-fL) / (N ^ ε * (2 : ℝ) ^ T) = N ^ (-fL) * q * (N ^ ε)⁻¹ := by
          rw [hq_def]; field_simp
      _ ≤ N ^ (-fL) * q * (J i / Λ) := by gcongr
      _ = N ^ (-fL) * J i * q / Λ := by ring
  have hgood_norm : ∀ i ∈ goodIdx, ∀ t ∈ block T (j i), ∀ y ∈ Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, y] (F i)| ≤ N ^ ε := by
    intro i hi t ht y hy
    rw [hblock] at ht
    have hR := quad_remez_parallelogram (hfq i) hq (hw0 i) hlam (hgood_vol i hi) t ht y
    obtain ⟨⟨l, t'⟩, hlt⟩ : (Pk i).Nonempty :=
      nonempty_of_measure_ne_zero (hfloorpos i).ne'
    have hl : l ∈ A' i := hlt.1
    have ht01 := hblock01 i t ht
    have hsp : |spatial l t| ≤ 2 * K := by
      unfold spatial
      have e1 : |t * l.2 1| ≤ K := by
        rw [abs_mul, abs_of_nonneg ht01.1]
        calc t * |l.2 1| ≤ 1 * K := mul_le_mul ht01.2 (hl.2 1) (abs_nonneg _) zero_le_one
          _ = K := one_mul K
      calc |l.2 0 + t * l.2 1| ≤ |l.2 0| + |t * l.2 1| := abs_add_le _ _
        _ ≤ 2 * K := by linarith [hl.2 0]
    have hc := (hconf i l hl t ht).1
    have hdist : |y - (c₀ i + c₁ i * t)| ≤ 1 + 2 * K + w i := by
      have hy' : |y| ≤ 1 := abs_le.mpr hy
      calc |y - (c₀ i + c₁ i * t)| = |y - spatial l t + (spatial l t - (c₀ i + c₁ i * t))| := by
            ring_nf
        _ ≤ |y - spatial l t| + |spatial l t - (c₀ i + c₁ i * t)| := abs_add_le _ _
        _ ≤ (|y| + |spatial l t|) + w i := by gcongr; exact abs_sub _ _
        _ ≤ 1 + 2 * K + w i := by linarith
    have hwpos := hw0 i
    have hratio : 3 + |y - (c₀ i + c₁ i * t)| / w i ≤ 4 + (1 + 2 * K) * (4 * N ^ h / b) := by
      have h1 : |y - (c₀ i + c₁ i * t)| / w i ≤ (1 + 2 * K) / w i + 1 := by
        rw [div_add_one hwpos.ne', div_le_div_iff_of_pos_right hwpos]
        linarith
      have h2 : 1 / w i ≤ 4 * N ^ h / b := by
        rw [div_le_div_iff₀ hwpos hb]
        linarith [hbw i hi]
      have h3 : (1 + 2 * K) / w i ≤ (1 + 2 * K) * (4 * N ^ h / b) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left h2 (by linarith)
      linarith
    have hA₀ : 0 ≤ A₀ := by rw [hA₀]; positivity
    have hpos : 0 ≤ 3 + |y - (c₀ i + c₁ i * t)| / w i := by positivity
    calc |MvPolynomial.eval ![t, y] (F i)| = |f i t y| := rfl
      _ ≤ 186624 * A₀ * (3 + |y - (c₀ i + c₁ i * t)| / w i) ^ 2 / lam ^ 4 := hR
      _ ≤ 186624 * A₀ * (4 + (1 + 2 * K) * (4 * N ^ h / b)) ^ 2 / lam ^ 4 := by gcongr
      _ ≤ N ^ ε := P4
  -- packets of a common world are almost disjoint
  have hPkdisj : ∀ i i', i ≠ i' → γ i = γ i' → μ (γ i) (Pk i ∩ Pk i') = 0 := by
    intro i i' hne hγ
    by_cases hj : j i = j i'
    · have hd := hdisj i i' hne hγ hj
      have : Pk i ∩ Pk i' = ∅ := by
        ext ⟨l, t⟩
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        exact Set.disjoint_left.mp hd h1.1.1 h2.1.1
      rw [this, measure_empty]
    · have := measure_blocks_inter_zero (hpt (γ i)) T hj (A' i) (A' i')
      rwa [hblock, hblock] at this
  -- aggregate discards
  set ω' : Fin W → ℝ≥0∞ := fun g => ENNReal.ofReal (ω g) with hω'
  have hXGsum := weighted_bad_le ω' μ γ Pk XG narrowIdx hPkm hXGm
    (fun i _ i' _ hne hγ => hPkdisj i i' hne hγ) hnarrow
  have hXLsum := weighted_bad_le ω' μ γ Pk XL thinIdx hPkm hXLm
    (fun i _ i' _ hne hγ => hPkdisj i i' hne hγ) hthin
  set U' : Fin W → Set (Coeff × ℝ) := fun g =>
    {p | ∃ i ∈ goodIdx, γ i = g ∧ p.1 ∈ A' i ∧ p.2 ∈ block T (j i)} with hU'
  have hUsub : ∀ g, {p : Coeff × ℝ | ∃ i, γ i = g ∧ p.1 ∈ A i ∧ p.2 ∈ block T (j i)} ⊆
      ((U' g ∪ ⋃ i ∈ narrowIdx.filter (fun i => γ i = g), Pk i) ∪
        ⋃ i ∈ thinIdx.filter (fun i => γ i = g), Pk i) ∪ {p : Coeff × ℝ | p.1 ∉ Good} := by
    intro g p hp
    obtain ⟨i, hγ, hA, hbl⟩ := hp
    by_cases hG : p.1 ∈ Good
    · left
      have hPk : p ∈ Pk i := ⟨⟨hA, hG⟩, by rw [← hblock]; exact hbl⟩
      by_cases hn : 4 * w i ≤ b * q
      · left; right
        exact Set.mem_biUnion (by simp [hnarrowIdx, hn, hγ]) hPk
      · rcases lt_or_ge (volume (Z i)) (ENNReal.ofReal (lam * (q * (2 * w i)))) with hz | hz
        · right
          exact Set.mem_biUnion (by simp [hthinIdx, hz, hγ, lt_of_not_ge hn]) hPk
        · left; left
          exact ⟨i, by simp [hgoodIdx, hz, lt_of_not_ge hn], hγ, ⟨hA, hG⟩, hbl⟩
    · right; exact hG
  have hUle : ∀ g, μ g {p : Coeff × ℝ | ∃ i, γ i = g ∧ p.1 ∈ A i ∧ p.2 ∈ block T (j i)} ≤
      μ g (U' g) + ∑ i ∈ narrowIdx.filter (fun i => γ i = g), μ g (Pk i) +
        ∑ i ∈ thinIdx.filter (fun i => γ i = g), μ g (Pk i) := by
    intro g
    calc _ ≤ μ g (((U' g ∪ ⋃ i ∈ narrowIdx.filter (fun i => γ i = g), Pk i) ∪
          ⋃ i ∈ thinIdx.filter (fun i => γ i = g), Pk i) ∪ {p : Coeff × ℝ | p.1 ∉ Good}) :=
          measure_mono (hUsub g)
      _ ≤ μ g ((U' g ∪ ⋃ i ∈ narrowIdx.filter (fun i => γ i = g), Pk i) ∪
          ⋃ i ∈ thinIdx.filter (fun i => γ i = g), Pk i) + μ g {p : Coeff × ℝ | p.1 ∉ Good} :=
          measure_union_le _ _
      _ = μ g ((U' g ∪ ⋃ i ∈ narrowIdx.filter (fun i => γ i = g), Pk i) ∪
          ⋃ i ∈ thinIdx.filter (fun i => γ i = g), Pk i) := by rw [hbadcoef, add_zero]
      _ ≤ μ g (U' g ∪ ⋃ i ∈ narrowIdx.filter (fun i => γ i = g), Pk i) +
          μ g (⋃ i ∈ thinIdx.filter (fun i => γ i = g), Pk i) := measure_union_le _ _
      _ ≤ (μ g (U' g) + μ g (⋃ i ∈ narrowIdx.filter (fun i => γ i = g), Pk i)) +
          μ g (⋃ i ∈ thinIdx.filter (fun i => γ i = g), Pk i) := by
          gcongr; exact measure_union_le _ _
      _ ≤ _ := by
          gcongr
          · exact measure_biUnion_finset_le _ _
          · exact measure_biUnion_finset_le _ _
  have hfib : ∀ S : Finset (Fin n), ∑ g, ω' g * ∑ i ∈ S.filter (fun i => γ i = g), μ g (Pk i) =
      ∑ i ∈ S, ω' (γ i) * μ (γ i) (Pk i) := by
    intro S
    rw [← Finset.sum_fiberwise S γ (fun i => ω' (γ i) * μ (γ i) (Pk i))]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [Finset.mem_filter] at hi
    rw [hi.2]
  set XGs := ∑ g, ω' g * μ g (XG g) with hXGs
  set XLs := ∑ g, ω' g * μ g (XL g) with hXLs
  have htot : ENNReal.ofReal Λ⁻¹ ≤ ∑ g, ω' g * μ g (U' g) + (2 * XGs + 2 * XLs) := by
    calc ENNReal.ofReal Λ⁻¹ ≤ ∑ g, ω' g *
          μ g {p : Coeff × ℝ | ∃ i, γ i = g ∧ p.1 ∈ A i ∧ p.2 ∈ block T (j i)} := hmass
      _ ≤ ∑ g, ω' g * (μ g (U' g) + ∑ i ∈ narrowIdx.filter (fun i => γ i = g), μ g (Pk i) +
          ∑ i ∈ thinIdx.filter (fun i => γ i = g), μ g (Pk i)) := by
          gcongr with g; exact hUle g
      _ = ∑ g, ω' g * μ g (U' g) +
          ∑ g, ω' g * ∑ i ∈ narrowIdx.filter (fun i => γ i = g), μ g (Pk i) +
          ∑ g, ω' g * ∑ i ∈ thinIdx.filter (fun i => γ i = g), μ g (Pk i) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun g _ => ?_)
          ring
      _ = ∑ g, ω' g * μ g (U' g) + ∑ i ∈ narrowIdx, ω' (γ i) * μ (γ i) (Pk i) +
          ∑ i ∈ thinIdx, ω' (γ i) * μ (γ i) (Pk i) := by rw [hfib, hfib]
      _ ≤ ∑ g, ω' g * μ g (U' g) + 2 * XGs + 2 * XLs := by gcongr
      _ = _ := by ring
  have hXfin : 2 * XGs + 2 * XLs ≠ ⊤ := by
    have hG' : XGs ≠ ⊤ := by
      rw [hXGs]
      refine ENNReal.sum_ne_top.mpr (fun g _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_)
      exact ne_top_of_le_ne_top (hfin g) (measure_mono (subset_univ _))
    have hL' : XLs ≠ ⊤ := by
      rw [hXLs]
      refine ENNReal.sum_ne_top.mpr (fun g _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_)
      exact ne_top_of_le_ne_top (hfin g) (measure_mono (subset_univ _))
    finiteness
  have hgoodtot : ENNReal.ofReal (N ^ (-ε)) ≤ ∑ g, ω' g * μ g (U' g) :=
    (ENNReal.add_le_add_iff_right hXfin).mp (P5.trans htot)
  -- the output, indexed by the good packets
  set m := goodIdx.card with hm
  let e : Fin m ≃ goodIdx := goodIdx.equivFin.symm
  refine ⟨T, m, fun k => γ (e k), fun k => j (e k), fun k => A' (e k), fun k => F (e k), hT,
    fun k => hA'm _, ?_, ?_, ?_⟩
  · intro k k' hkk hγ hj
    have hne : (e k : Fin n) ≠ e k' := fun h => hkk (e.injective (Subtype.ext h))
    exact (hdisj _ _ hne hγ hj).mono Set.inter_subset_left Set.inter_subset_left
  · intro k
    have hi := (e k).2
    refine ⟨(hpk _).1, hgood_norm _ hi, ?_, ?_⟩
    · intro l hl t ht
      have := (hconf _ l hl t (by rw [← hblock]; exact ht)).2
      exact this.trans (mul_le_mul_of_nonneg_right P6 ha.le)
    · have := hgood_floor _ hi
      simp only [hPk] at this
      rw [hblock]
      exact this
  · calc ENNReal.ofReal (N ^ (-ε)) ≤ ∑ g, ω' g * μ g (U' g) := hgoodtot
      _ ≤ _ := by
        gcongr with g
        intro p hp
        obtain ⟨i, hi, hγ, hA, hbl⟩ := hp
        refine ⟨e.symm ⟨i, hi⟩, ?_, ?_, ?_⟩
        · simp [hγ]
        · simpa using hA
        · simpa using hbl

end Submission.Obl.k4_scalar_terminal_chart_packet_extraction
