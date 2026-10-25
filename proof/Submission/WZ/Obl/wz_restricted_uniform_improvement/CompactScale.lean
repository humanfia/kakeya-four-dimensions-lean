-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_restricted_uniform_improvement.CompactScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_restricted_uniform_improvement.Refinement

namespace WangZahlLot.Obl.wz_restricted_uniform_improvement

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_endpoint_bootstrap

/-- A fixed contraction of one tube lies in every sufficiently nearby tube. -/
theorem contracted_tube_subset {δ : ℝ} (hδ : 0 < δ) (x v y w : Space)
    (hx : ‖x - y‖ ≤ δ / 40) (hv : ‖v - w‖ ≤ δ / 40) :
    AffineMap.homothety x (9 / 10 : ℝ) '' tube δ x v ⊆ tube δ y w := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  apply mem_thickening_iff.mpr
  refine ⟨y + ((9 / 10 : ℝ) * t) • w, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨(9 / 10 : ℝ) * t, ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩, by simp⟩
  · have hcoeff : 0 ≤ (9 / 10 : ℝ) * t ∧ (9 / 10 : ℝ) * t ≤ 1 := by
      constructor <;> nlinarith [ht.1, ht.2]
    have hn : ‖((9 / 10 : ℝ) * t) • (v - w)‖ ≤ ‖v - w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoeff.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hcoeff.2
    have heq : AffineMap.homothety x (9 / 10 : ℝ) p - (y + ((9 / 10 : ℝ) * t) • w) =
        (9 / 10 : ℝ) • (p - (x + t • v)) + (x - y) + ((9 / 10 : ℝ) * t) • (v - w) := by
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      module
    rw [dist_eq_norm, heq]
    calc
      _ ≤ ‖(9 / 10 : ℝ) • (p - (x + t • v))‖ + ‖x - y‖ +
          ‖((9 / 10 : ℝ) * t) • (v - w)‖ := (norm_add_le _ _).trans
        (add_le_add_left (norm_add_le _ _) _)
      _ ≤ (9 / 10 : ℝ) * ‖p - (x + t • v)‖ + δ / 40 + δ / 40 := by
        have hnorm : ‖(9 / 10 : ℝ) • (p - (x + t • v))‖ =
            (9 / 10 : ℝ) * ‖p - (x + t • v)‖ := by rw [norm_smul]; norm_num
        rw [hnorm]
        exact add_le_add (add_le_add_right hx _) (hn.trans hv)
      _ < δ := by rw [dist_eq_norm] at hpq; linarith

/-- Essential distinctness separates the parameters at a fixed fraction of the radius. -/
theorem tube_parameters_separated {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {x v y w : Space} (hv : ‖v‖ = 1)
    (hhalf : volume (tube δ x v ∩ tube δ y w) ≤
      (1 / 2 : ENNReal) * volume (tube δ x v)) :
    δ / 40 < dist (x, v) (y, w) := by
  by_contra hdist
  have hdist' : max (dist x y) (dist v w) ≤ δ / 40 := by
    simpa only [Prod.dist_eq] using not_lt.mp hdist
  have hx : ‖x - y‖ ≤ δ / 40 := by
    simpa only [dist_eq_norm] using (max_le_iff.mp hdist').1
  have hvw : ‖v - w‖ ≤ δ / 40 := by
    simpa only [dist_eq_norm] using (max_le_iff.mp hdist').2
  have hsub : AffineMap.homothety x (9 / 10 : ℝ) '' tube δ x v ⊆
      tube δ x v ∩ tube δ y w :=
    subset_inter (contracted_tube_subset hδ x v x v (by simp; positivity) (by simp; positivity))
      (contracted_tube_subset hδ x v y w hx hvw)
  have hvol := (measure_mono (μ := volume) hsub).trans hhalf
  rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin] at hvol
  have hfinite : volume (tube δ x v) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (tube_volume_upper hδ hδ1 x v hv)
  have hpos : 0 < (volume (tube δ x v)).toReal := by
    have hlower := WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hδ x v hv
    have h := ENNReal.toReal_mono hfinite hlower
    rw [ENNReal.toReal_ofReal (sq_nonneg δ)] at h
    exact (sq_pos_of_pos hδ).trans_le h
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hfinite) hvol
  norm_num [ENNReal.toReal_mul] at h
  linarith

/-- Compact scale intervals admit a uniform cardinality bound. Only compactness
of the parameter space is used; no asymptotic packing exponent is needed. -/
theorem cardinality_on_compact_scales (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (δ η : ℝ), δ₀ ≤ δ → δ ≤ (1 / 100 : ℝ) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Admissible δ η x v Y → (n : ℝ) ≤ M := by
  classical
  obtain ⟨F, _, _, hcover⟩ :=
    WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.exists_finset_separated_cover
      (isCompact_closedBall (0 : Space × Space) 1).totallyBounded
      (show 0 < δ₀ / 100 by positivity)
  refine ⟨max 1 (F.card : ℝ), le_max_left _ _, ?_⟩
  intro δ η hδ₀δ hδ100 n x v Y hA
  have hδ : 0 < δ := hδ₀.trans_le hδ₀δ
  have hδ1 : δ ≤ 1 := by linarith
  have hparam : ∀ i, (x i, v i) ∈ closedBall (0 : Space × Space) 1 := by
    intro i
    have hx : ‖x i‖ < 1 := by
      have h := hA.2.2.1 i (self_subset_thickening hδ _ (left_mem_segment ℝ (x i) (x i + v i)))
      simpa only [mem_ball, dist_zero_right] using h
    simpa only [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] using And.intro hx.le (hA.2.1 i).le
  have hex : ∀ i, ∃ z : F, dist (x i, v i) (z : Space × Space) ≤ δ₀ / 100 := by
    intro i
    obtain ⟨z, hz, hiz⟩ := mem_iUnion₂.mp (hcover (hparam i))
    exact ⟨⟨z, hz⟩, mem_closedBall.mp hiz⟩
  choose g hg using hex
  have hg_inj : Function.Injective g := by
    intro i j hij
    by_contra hne
    have hsep := tube_parameters_separated hδ hδ1 (hA.2.1 i) (hA.2.2.2.1 i j hne)
    have hi := hg i
    have hj := hg j
    have htri := dist_triangle (x i, v i) (g i : Space × Space) (x j, v j)
    rw [hij, dist_comm (g j : Space × Space) (x j, v j)] at htri
    rw [hij] at hi
    linarith
  have hcard : n ≤ F.card := by simpa using Fintype.card_le_of_injective g hg_inj
  exact (Nat.cast_le.mpr hcard).trans (le_max_right _ _)

/-- Average shading density always gives a lower bound from one average tube. -/
theorem average_union_lower {δ η : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hδ : 0 < δ) (hA : Admissible δ η x v Y) :
    ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (⋃ i, Y i) := by
  have hsub : (⋃ i, Y i) ⊆ ball (0 : Space) 1 :=
    iUnion_subset fun i => (hA.2.2.2.2.2.1 i).trans (hA.2.2.1 i)
  have hfin : volume (⋃ i, Y i) ≠ ⊤ := ne_top_of_le_ne_top measure_ball_ne_top (measure_mono hsub)
  have hsum : ∑ i, volume (Y i) ≤ (n : ENNReal) * volume (⋃ i, Y i) := by
    calc
      _ ≤ ∑ i : Fin n, volume (⋃ j, Y j) :=
        Finset.sum_le_sum fun i _ => measure_mono (subset_iUnion Y i)
      _ = _ := by simp
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin)
    (hA.2.2.2.2.2.2.trans hsum)
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  have hr : δ ^ η * δ ^ 2 ≤ (volume (⋃ i, Y i)).toReal := by
    apply (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hA.1 : (0 : ℝ) < n)).mp
    nlinarith only [h]
  exact (ENNReal.ofReal_le_ofReal hr).trans_eq (ENNReal.ofReal_toReal hfin)

/-- On any compact interval of positive scales, the restricted bound follows
from average density and essential distinctness alone. -/
theorem compact_restricted_bound (σ ω η δ₀ : ℝ)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 2 / 3) (hω : 0 ≤ ω) (hη : 0 ≤ η) (hδ₀ : 0 < δ₀) :
    ∃ a : ℝ, 0 < a ∧ ∀ ε δ : ℝ, 0 ≤ ε → δ₀ ≤ δ → δ ≤ (1 / 100 : ℝ) →
      ∀ m : ℝ, 1 ≤ m → ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Admissible δ η x v Y →
      ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) *
        (m ^ (-(3 / 2 : ℝ)) * ((n : ℝ) * δ)) ^ (-σ)) ≤ volume (⋃ i, Y i) := by
  obtain ⟨M, hM, hcard⟩ := cardinality_on_compact_scales δ₀ hδ₀
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  let a := δ₀ ^ η / (M * δ₀ ^ (-σ))
  have ha : 0 < a := div_pos (Real.rpow_pos_of_pos hδ₀ _) (by positivity)
  refine ⟨a, ha, ?_⟩
  intro ε δ hε hδ₀δ hδ100 m hm n x v Y hA
  have hδ : 0 < δ := hδ₀.trans_le hδ₀δ
  have hδ1 : δ ≤ 1 := by linarith
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hA.1
  have hnM := hcard δ η hδ₀δ hδ100 n x v Y hA
  have hpow : ((n : ℝ) * δ) ^ (-σ) ≤ δ₀ ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hδ₀
      (hδ₀δ.trans (le_mul_of_one_le_left hδ.le hn)) (neg_nonpos.mpr hσ)
  have hcoef : restrictedCoefficient σ δ m (n : ℝ) ≤ M * δ ^ 2 * δ₀ ^ (-σ) := by
    apply (restrictedCoefficient_le hσ1 hm (Nat.cast_nonneg n) hδ.le).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_right hnM (sq_nonneg δ)) hpow
      (Real.rpow_nonneg (by positivity) _) (by positivity)
  have heps : δ ^ (ω + ε) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (add_nonneg hω hε)
  apply le_trans (ENNReal.ofReal_le_ofReal _) (average_union_lower hδ hA)
  calc
    _ = a * δ ^ (ω + ε) * restrictedCoefficient σ δ m (n : ℝ) := by
      unfold restrictedCoefficient
      ring
    _ ≤ a * 1 * (M * δ ^ 2 * δ₀ ^ (-σ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left heps ha.le) hcoef
        (restrictedCoefficient_nonneg (by linarith) (Nat.cast_nonneg n) hδ.le) (by positivity)
    _ = δ₀ ^ η * δ ^ 2 := by
      dsimp [a]
      have hpowne := (Real.rpow_pos_of_pos hδ₀ (-σ)).ne'
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hδ₀.le hδ₀δ hη) (sq_nonneg δ)

/-- It suffices to establish the restricted estimate at sufficiently small scales.
The small-scale cutoff may depend on all the estimate's parameters. -/
def AsymptoticRestricted (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → δ ≤ δ₀ →
    ∀ m : ℝ, 1 ≤ m → ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Admissible δ η x v Y → Katz δ m x v → Frostman δ (δ ^ (-η)) x v →
    ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) *
      (m ^ (-(3 / 2 : ℝ)) * ((n : ℝ) * δ)) ^ (-σ)) ≤ volume (⋃ i, Y i)

theorem restricted_of_asymptotic {σ ω : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 2 / 3)
    (hω : 0 ≤ ω) (h : AsymptoticRestricted σ ω) : Restricted σ ω := by
  intro ε hε
  obtain ⟨a, ha, η, hη, δ₀, hδ₀, hsmall⟩ := h ε hε
  obtain ⟨b, hb, hlarge⟩ := compact_restricted_bound σ ω η δ₀ hσ hσ1 hω hη.le hδ₀
  refine ⟨min a b, lt_min ha hb, η, hη, ?_⟩
  intro δ hδ hδ100 m hm n x v Y hA hK hF
  by_cases hδsmall : δ ≤ δ₀
  · apply le_trans (ENNReal.ofReal_le_ofReal _) (hsmall δ hδ hδ100 hδsmall m hm n x v Y hA hK hF)
    gcongr
    exact min_le_left _ _
  · apply le_trans (ENNReal.ofReal_le_ofReal _)
      (hlarge ε δ hε.le (le_of_not_ge hδsmall) hδ100 m hm n x v Y hA)
    gcongr
    exact min_le_right _ _

end WangZahlLot.Obl.wz_restricted_uniform_improvement
