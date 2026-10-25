-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_kaufman_projection_count.Kaufman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_kaufman_projection_count.KaufmanCore
import Submission.WZ.Obl.wz_slab_local_linearity.SmallPowers

/- Adapted from this tree’s o103 branch x0272, commit f2e1c96. -/

namespace WangZahlLot.Obl.wz_kaufman_projection_count

open Set Metric

/-- Kaufman projection counting in the exact interface of the proposed child. -/
theorem kaufman_projection_count : ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ C d : ℝ, 0 < δ → δ ≤ δ₀ → 1 ≤ C → 0 < d → ∀ (F Λ : Set (EuclideanSpace ℝ (Fin 2))) (H : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), F.Finite → Λ.Finite → (∀ θ ∈ Λ, ‖θ‖ = 1) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((F ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * F.ncard ∧ ((Λ ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * Λ.ncard) → H ⊆ Λ ×ˢ F → H.Nonempty → d * Λ.ncard * F.ncard ≤ H.ncard → ∃ θ ∈ Λ, ∀ (m : ℕ) (cc : Fin m → ℝ), {t : ℝ | ∃ a, (θ, a) ∈ H ∧ t = inner ℝ θ a} ⊆ (⋃ j, Metric.closedBall (cc j) δ) → d ^ 3 * δ ^ (ε - 1) ≤ C ^ 2 * m := by
  classical
  intro ε hε
  let γ : ℝ := 1 - min (ε / 2) (1 / 2)
  have hγ : 0 ≤ γ := by dsimp [γ]; linarith [min_le_right (ε / 2) (1 / 2 : ℝ)]
  have hγ1 : γ < 1 := by
    dsimp [γ]
    have hp : 0 < min (ε / 2) (1 / 2 : ℝ) := by positivity
    linarith
  have hslack : 0 < ε + γ - 1 := by dsimp [γ]; linarith [min_le_left (ε / 2) (1 / 2 : ℝ)]
  obtain ⟨ρ₀, hρ₀, hbudget⟩ :=
    WangZahlLot.Obl.wz_slab_local_linearity.exists_small_monomial
      (C := 8 * energyConstant γ) (a := ε + γ - 1) (b := 0) hslack
      (mul_pos (by norm_num) (energyConstant_pos hγ1))
  refine ⟨min 1 ρ₀, lt_min zero_lt_one hρ₀, ?_⟩
  intro δ C d hδ hsmall hC hd F Λ H hF hΛ hunit hFr hH hHne hdensity
  have hδ1 : δ ≤ 1 := hsmall.trans (min_le_left _ _)
  have hHfin : H.Finite := (hΛ.prod hF).subset hH
  let S : Finset Plane := hF.toFinset
  let T : Finset Plane := hΛ.toFinset
  let J : Finset (Plane × Plane) := hHfin.toFinset
  have hSset : (↑S : Set Plane) = F := hF.coe_toFinset
  have hTset : (↑T : Set Plane) = Λ := hΛ.coe_toFinset
  have hScard : (S.card : ℝ) = (F.ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card F hF]
  have hTcard : (T.card : ℝ) = (Λ.ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card Λ hΛ]
  have hJcard : (J.card : ℝ) = (H.ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card H hHfin]
  have hSF : ClosedFiniteFrostman δ C S := by
    intro x r hr
    simpa only [hSset, hScard] using (hFr x r hr).1
  have hTF : ClosedFiniteFrostman δ C T := by
    intro x r hr
    simpa only [hTset, hTcard] using (hFr x r hr).2
  have hJ : J ⊆ T ×ˢ S := by
    intro p hp
    have hh := hH (hHfin.mem_toFinset.mp hp)
    exact Finset.mem_product.mpr ⟨hΛ.mem_toFinset.mpr hh.1, hF.mem_toFinset.mpr hh.2⟩
  obtain ⟨p, hp⟩ := hHne
  have hpJ : p ∈ J := hHfin.mem_toFinset.mpr hp
  have hJne : J.Nonempty := ⟨p, hpJ⟩
  have hden : d * (T.card : ℝ) * (S.card : ℝ) ≤ (J.card : ℝ) := by
    rw [hTcard, hScard, hJcard]
    exact hdensity
  have hSpos : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨p.2, (Finset.mem_product.mp (hJ hpJ)).2⟩
  have hTpos : (0 : ℝ) < T.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨p.1, (Finset.mem_product.mp (hJ hpJ)).1⟩
  have hcap : (J.card : ℝ) ≤ (T.card : ℝ) * (S.card : ℝ) := by
    have hc := Finset.card_le_card hJ
    rw [Finset.card_product] at hc
    exact_mod_cast hc
  have hd1 : d ≤ 1 := by
    apply (mul_le_mul_iff_left₀ (mul_pos hTpos hSpos)).mp
    nlinarith [hden.trans hcap]
  obtain ⟨θ, hθ, hgain⟩ := finite_kaufman_energy_gain hSF hTF hδ hδ1 hC hd
    (fun θ hθ => hunit θ (hΛ.mem_toFinset.mp hθ)) hγ hγ1 hJ hJne hden
  refine ⟨θ, hΛ.mem_toFinset.mp hθ, ?_⟩
  intro m cc hc
  have hcov : Covers δ ((fun x => inner ℝ θ x) '' (↑(graphFiber S J θ) : Set Plane)) cc := by
    rintro t ⟨x, hx, rfl⟩
    have hxJ : (θ, x) ∈ J := (Finset.mem_filter.mp hx).2
    exact hc ⟨x, hHfin.mem_toFinset.mp hxJ, rfl⟩
  have hg := hgain m cc hcov
  have hd3 : d ^ 3 ≤ d ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hd1)]
  have hb : 8 * energyConstant γ * δ ^ (ε + γ - 1) ≤ 1 := by
    simpa only [Real.rpow_zero] using hbudget δ hδ (hsmall.trans (min_le_right _ _))
  calc d ^ 3 * δ ^ (ε - 1) ≤ d ^ 2 * δ ^ (ε - 1) :=
        mul_le_mul_of_nonneg_right hd3 (by positivity)
    _ ≤ ((8 * C ^ 2 * energyConstant γ * δ ^ γ) * (m : ℝ)) * δ ^ (ε - 1) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
    _ = (C ^ 2 * (m : ℝ)) * (8 * energyConstant γ * δ ^ (ε + γ - 1)) := by
      rw [show ε + γ - 1 = γ + (ε - 1) by ring, Real.rpow_add hδ]
      ring
    _ ≤ (C ^ 2 * (m : ℝ)) * 1 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := mul_one _

end WangZahlLot.Obl.wz_kaufman_projection_count
