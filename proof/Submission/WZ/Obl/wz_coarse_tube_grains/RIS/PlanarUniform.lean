-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PlanarUniform.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PlanarTwoScales
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.BroadVolume
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.DyadicPower

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

set_option maxHeartbeats 800000 in
/-- The planar selection step: a broad, dense family of polynomially bounded
cardinality and near-minimal volume has a mass-retaining planar refinement
with uniform multiplicity and a matching lower volume bound. -/
theorem planar_uniform_two_scales {ε β D : ℝ} (hε : 0 < ε) (hβ : 0 < β) (hD : 0 < D) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ δ ρ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d → δ / 100 ≤ ρ → ρ ≤ 1 / 100 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), 0 < n →
        (n : ℝ) ≤ δ ^ (-D) →
        (∀ i, ‖v i‖ = 1) → (∀ i, Tube ρ (x i) (v i) ⊆ Metric.ball 0 1) →
        (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ Tube ρ (x i) (v i)) →
        ENNReal.ofReal (δ ^ η * (n : ℝ) * ρ ^ 2) ≤ ∑ i, volume (Y i) →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (-η) * ρ) →
        (∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ 1 →
          ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s}.ncard : ℝ) ≤
            (δ ^ (-η) * s ^ β) * incidence Y p) →
        ∃ (e : Space) (t M : ℝ) (Z : Fin n → Set Space), ‖e‖ = 1 ∧ 0 < M ∧
          (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
          (∀ i, (Z i).Nonempty → Tube ρ (x i) (v i) ⊆ {p | |inner ℝ e p - t| ≤ 2 * ρ}) ∧
          ENNReal.ofReal (δ ^ ε) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
          ENNReal.ofReal (δ ^ ε * ρ) ≤ volume (⋃ i, Z i) ∧
          (∀ p ∈ ⋃ i, Z i, M ≤ incidence Z p ∧ incidence Z p ≤ 2 * M) := by
  let Q := 4 / β + 8
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hQ8 : 8 ≤ Q := by
    dsimp [Q]
    have hh : 0 ≤ 4 / β := by positivity
    linarith
  let τ := min (β / 16) (min (ε / (4 * (Q + 1))) (1 / 16))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτβ : τ ≤ β / 16 := min_le_left _ _
  have hτε : τ ≤ ε / (4 * (Q + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hτQ : 4 * (Q + 1) * τ ≤ ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * (Q + 1))).mp hτε
    nlinarith only [hh]
  have h3τε : 3 * τ ≤ ε := by nlinarith
  have hQτε : Q * τ < ε := by nlinarith
  obtain ⟨η₀, hη₀, hη₀1, d₁, hd₁, hplane⟩ := planar_concentration_two_scales hτ hβ
  let η := min η₀ τ
  have hη : 0 < η := lt_min hη₀ hτ
  have hη₀' : η ≤ η₀ := min_le_left _ _
  have hητ : η ≤ τ := min_le_right _ _
  have hη1 : η ≤ 1 := hη₀'.trans hη₀1
  obtain ⟨d₂, hd₂, hdyadic⟩ := dyadic_shading_refinement_common_power hD hτ
  obtain ⟨d₃, hd₃, hcut₃⟩ := exists_power_cutoff hτ (c := 1 / 2) (by norm_num)
  obtain ⟨d₄, hd₄, hcut₄⟩ := exists_power_cutoff (sub_pos.mpr hQτε)
    (c := 1 / 8192) (by norm_num)
  refine ⟨η, hη, hη1, min d₁ (min d₂ (min d₃ d₄)),
    lt_min hd₁ (lt_min hd₂ (lt_min hd₃ hd₄)), ?_⟩
  intro δ ρ hδ hδ100 hδd hδρ hρ100 n x v Y hn hnD hv hT hY hYT hdense hvol hbroad
  have hδ1 : δ ≤ 1 := by linarith
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity : 0 < δ / 100) hδρ
  have hδd₁ : δ ≤ d₁ := hδd.trans (min_le_left _ _)
  have hδd₂ : δ ≤ d₂ := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd₃ : δ ≤ d₃ := hδd.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd₄ : δ ≤ d₄ := hδd.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hc₃ := hcut₃ δ hδ hδd₃
  have hc₄ := hcut₄ δ hδ hδd₄
  have hneg : δ ^ (-η) ≤ δ ^ (-η₀) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hη₀')
  obtain ⟨e, t, F, he, hslab, hretain⟩ := hplane δ ρ hδ hδ100 hδd₁ hδρ hρ100 n x v Y hn hv hT hY hYT
    ((ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη₀')
        (Nat.cast_nonneg n)) (sq_nonneg ρ))).trans hdense)
    (hvol.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hneg hρ.le)))
    (fun p u s hu hs hs1 => (hbroad p u s hu hs hs1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hneg
        (Real.rpow_nonneg (hδ.le.trans hs) _)) (incidence_nonneg Y p)))
  let U := fun i => if i ∈ F then Y i else ∅
  have hU : ∀ i, MeasurableSet (U i) ∧ U i ⊆ Y i := by
    intro i
    dsimp [U]
    split_ifs
    · exact ⟨hY i, subset_rfl⟩
    · exact ⟨MeasurableSet.empty, empty_subset _⟩
  have hYfin : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono ((hYT i).trans (hT i)))
  have hUfin : ∀ i, volume (U i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hYfin i) (measure_mono (hU i).2)
  have hUsum : (∑ i, volume (U i)) = ∑ i ∈ F, volume (Y i) := by
    simp only [U, apply_ite volume, measure_empty]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hUkeep : δ ^ τ * shadingMass Y ≤ shadingMass U := by
    have hh := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i _ => hUfin i)
      (hUsum.symm ▸ hretain)
    simpa only [shadingMass, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _),
      ENNReal.toReal_sum (fun i _ => hYfin i), ENNReal.toReal_sum (fun i _ => hUfin i)] using hh
  let θ := δ ^ τ / 2
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  obtain ⟨W, hW, hWkeep, hrelative⟩ := relative_incidence_refinement hY
    (fun i => (hU i).1) hYfin (fun i => (hU i).2) hθ
  have hWY : ∀ i, W i ⊆ Y i := fun i => (hW i).2.trans (hU i).2
  have hWfin : ∀ i, volume (W i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hYfin i) (measure_mono (hWY i))
  have hWkeep' : δ ^ τ / 2 * shadingMass Y ≤ shadingMass W := by dsimp [θ] at hWkeep; linarith
  obtain ⟨k, Z, hZ, hZkeep, hlevel⟩ := hdyadic δ hδ hδd₂ n hnD W (fun i => (hW i).1)
  have hZY : ∀ i, Z i ⊆ Y i := fun i => (hZ i).2.trans (hWY i)
  have hZfin : ∀ i, volume (Z i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hYfin i) (measure_mono (hZY i))
  have hsumZ : (∑ i, volume (Z i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hZfin i
  have hZkeepR : δ ^ τ * shadingMass W ≤ shadingMass Z := by
    have hh := ENNReal.toReal_mono hsumZ hZkeep
    simpa only [shadingMass, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _),
      ENNReal.toReal_sum (fun i _ => hWfin i), ENNReal.toReal_sum (fun i _ => hZfin i)] using hh
  have hmassY : 0 ≤ shadingMass Y := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have h3τ : δ ^ (3 * τ) * shadingMass Y ≤ shadingMass Z := by
    calc
      _ = δ ^ τ * (δ ^ τ * (δ ^ τ * shadingMass Y)) := by
        rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ δ ^ τ * (δ ^ τ / 2 * shadingMass Y) := by
        have hh := mul_le_mul_of_nonneg_right hc₃ (mul_nonneg (Real.rpow_nonneg hδ.le τ) hmassY)
        have hh' : δ ^ τ * (δ ^ τ * shadingMass Y) ≤ δ ^ τ / 2 * shadingMass Y := by
          convert hh using 1 <;> ring
        exact mul_le_mul_of_nonneg_left hh' (Real.rpow_nonneg hδ.le _)
      _ ≤ δ ^ τ * shadingMass W := mul_le_mul_of_nonneg_left hWkeep' (Real.rpow_nonneg hδ.le _)
      _ ≤ _ := hZkeepR
  have hrelativeZ : ∀ p ∈ ⋃ i, Z i, θ * incidence Y p ≤ incidence Z p := by
    intro p hp
    have heq : incidence Z p = incidence W p := by
      have hs : {i | p ∈ Z i} = {i | p ∈ W i} := by
        ext i
        exact (hlevel p hp).2.2 i
      rw [incidence_eq_ncard, incidence_eq_ncard, hs]
    rw [heq]
    exact hrelative p ((iUnion_mono fun i => (hZ i).2) hp)
  let b := δ ^ (4 * τ / β)
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have hδb : δ ≤ b := by
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1
           ((div_le_iff₀ hβ).mpr (by linarith))
  have hcapcoef : δ ^ (-η) * b ^ β ≤ θ / 2 := by
    have heq : δ ^ (-η) * b ^ β = δ ^ (4 * τ - η) := by
      dsimp [b]
      rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
      congr 1
      field_simp
      ring
    rw [heq]
    calc
      _ ≤ δ ^ (3 * τ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = δ ^ τ * (δ ^ τ) ^ 2 := by
        rw [← Real.rpow_natCast (δ ^ τ), ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
        congr 1
        norm_num
        ring
      _ ≤ θ / 2 := by
        have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.rpow_nonneg hδ.le _) hc₃ 2)
          (Real.rpow_nonneg hδ.le τ)
        dsimp [θ]
        nlinarith only [hh]
  have hZbroad := broadness_of_relative_incidence v hZY hrelativeZ (le_refl (θ / 2))
    (fun p u hu => (hbroad p u b hu hδb hb1).trans
      (mul_le_mul_of_nonneg_right hcapcoef (incidence_nonneg Y p)))
  have hYsumfin : (∑ i, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hYfin i
  have hdenseR : δ ^ η * (n : ℝ) * ρ ^ 2 ≤ shadingMass Y := by
    have hh := (ENNReal.ofReal_le_iff_le_toReal hYsumfin).mp hdense
    simpa only [shadingMass, ENNReal.toReal_sum (fun i _ => hYfin i)] using hh
  have hZdensity : δ ^ (4 * τ) * (n : ℝ) * ρ ^ 2 ≤ shadingMass Z := by
    calc
      _ ≤ δ ^ (3 * τ + η) * (n : ℝ) * ρ ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
            (Nat.cast_nonneg n)) (sq_nonneg ρ)
      _ = δ ^ (3 * τ) * (δ ^ η * (n : ℝ) * ρ ^ 2) := by rw [Real.rpow_add hδ]; ring
      _ ≤ δ ^ (3 * τ) * shadingMass Y := mul_le_mul_of_nonneg_left hdenseR (Real.rpow_nonneg hδ.le _)
      _ ≤ _ := h3τ
  have hZunionfin : volume (⋃ i, Z i) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((measure_mono (iUnion_mono hZY)).trans hvol)
  have hZvolume := broad_union_volume_lower hρ hb hb1 (Real.rpow_pos_of_pos hδ (4 * τ)) hn
    x v Z hv (fun i => (hZ i).1) (fun i => (hZY i).trans (hYT i)) hZunionfin hZdensity hZbroad
  have hvolcoef : δ ^ ε * ρ ≤ b * (δ ^ (4 * τ)) ^ 2 * ρ / 8192 := by
    have heq : b * (δ ^ (4 * τ)) ^ 2 = δ ^ (Q * τ) := by
      dsimp [b]
      rw [← Real.rpow_natCast (δ ^ (4 * τ)), ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
      norm_num only [Nat.cast_ofNat]
      congr 1
      dsimp [Q]
      ring
    rw [heq]
    calc
      _ = (δ ^ (ε - Q * τ) * δ ^ (Q * τ)) * ρ := by rw [← Real.rpow_add hδ]; congr 2; ring
      _ ≤ ((1 / 8192) * δ ^ (Q * τ)) * ρ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc₄ (Real.rpow_nonneg hδ.le _)) hρ.le
      _ = _ := by ring
  refine ⟨e, t, (2 : ℝ) ^ k, Z, he, by positivity, fun i => ⟨(hZ i).1, hZY i⟩, ?_, ?_,
    (ENNReal.ofReal_le_ofReal hvolcoef).trans hZvolume, ?_⟩
  · intro i hi
    have hiF : i ∈ F := by
      obtain ⟨p, hp⟩ := hi
      have hpU := (hW i).2 ((hZ i).2 hp)
      by_contra hiF
      simp only [U, ite_eq_right hiF, mem_empty_iff_false] at hpU
    exact hslab i hiF
  · apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYsumfin) hsumZ).mp
    have hh := (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 h3τε) hmassY).trans h3τ
    simpa only [shadingMass, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _),
      ENNReal.toReal_sum (fun i _ => hYfin i), ENNReal.toReal_sum (fun i _ => hZfin i)] using hh
  · intro p hp
    rw [incidence_eq_card_through]
    constructor
    · exact_mod_cast (hlevel p hp).1
    · have hh : ((Finset.univ.filter fun i => p ∈ Z i).card : ℝ) < (2 : ℝ) ^ (k + 1) := by
        exact_mod_cast (hlevel p hp).2.1
      rw [pow_succ] at hh
      change ((Finset.univ.filter fun i => p ∈ Z i).card : ℝ) ≤ 2 * (2 : ℝ) ^ k
      linarith

/-- The equal-scale version of planar uniform refinement. -/
theorem planar_uniform_refinement {ε β D : ℝ} (hε : 0 < ε) (hβ : 0 < β) (hD : 0 < D) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), 0 < n →
        (n : ℝ) ≤ δ ^ (-D) →
        (∀ i, ‖v i‖ = 1) → (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
        (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ Tube δ (x i) (v i)) →
        ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i) →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (1 - η)) →
        (∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ 1 →
          ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ s}.ncard : ℝ) ≤
            (δ ^ (-η) * s ^ β) * incidence Y p) →
        ∃ (e : Space) (t M : ℝ) (Z : Fin n → Set Space), ‖e‖ = 1 ∧ 0 < M ∧
          (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
          (∀ i, (Z i).Nonempty → Tube δ (x i) (v i) ⊆ {p | |inner ℝ e p - t| ≤ 2 * δ}) ∧
          ENNReal.ofReal (δ ^ ε) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
          ENNReal.ofReal (δ ^ (1 + ε)) ≤ volume (⋃ i, Z i) ∧
          (∀ p ∈ ⋃ i, Z i, M ≤ incidence Z p ∧ incidence Z p ≤ 2 * M) := by
  obtain ⟨η, hη, hη1, d, hd, hrefine⟩ := planar_uniform_two_scales hε hβ hD
  refine ⟨η, hη, hη1, d, hd, ?_⟩
  intro δ hδ hδ100 hδd n x v Y hn hnD hv hT hY hYT hdense hvol hbroad
  have hvol' : volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (-η) * δ) := by
    have he : δ ^ (1 - η) = δ ^ (-η) * δ := by
      rw [show 1 - η = -η + 1 by ring, Real.rpow_add hδ, Real.rpow_one]
    simpa only [he] using hvol
  have hh := hrefine δ δ hδ hδ100 hδd (by linarith) hδ100 n x v Y
    hn hnD hv hT hY hYT hdense hvol' hbroad
  have he : δ ^ ε * δ = δ ^ (1 + ε) := by
    rw [Real.rpow_add hδ, Real.rpow_one, mul_comm]
  simpa only [he] using hh

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
