import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.GoodDataOfAE

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Simultaneous original short-domain witnesses for the three literal
layers. The cost uses their original reference budgets, and every later
pair restriction may keep these stored witnesses unchanged. -/
theorem exists_stored_short_witnesses (hp : p.Valid)
    {k : ℕ} {r u v m H δ : ℝ} (hH : 1 ≤ H) (hδ : 0 < δ)
    (L : Fin 3 → ProjectedLayer α)
    (hL : ∀ a, (L a).Valid p k (![r, r + u, r + v] a) m H)
    (hbβ : ∀ a, (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r) ≤ (L a).β)
    (hβg : ∀ a, (L a).β ≤ p.N k ^ (-p.ℓ * r))
    (σ : Measure (α × ℝ)) (hσ : σ ≤ p.ρ k) (hcover : ∀ a, (L a).Covers σ) :
    ∃ θ : Measure (α × ℝ), θ ≤ σ ∧
      σ univ ≤ θ univ + ENNReal.ofReal (720 * δ * H ^ 3) ∧
      ∀ᵐ ω ∂θ, p.StoredWitnessAt k r u v m δ L θ ω := by
  classical
  let h : ℝ := (2 : ℝ) ^ (-(p.T k r : ℤ))
  let g : ℝ := p.N k ^ (-p.ℓ * r)
  let b : ℝ := h * g
  have hN : 0 < p.N k := by linarith [hp.scale k]
  have hh : 0 < h := by dsimp [h]; positivity
  have hg : 0 < g := by dsimp [g]; positivity
  have hb : 0 < b := mul_pos hh hg
  have hh1 : h ≤ 1 := by
    dsimp [h]
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  obtain ⟨menus, θ, S, hθ, hmass, hfloor, hretained⟩ :=
    ProjectedLayer.prepare_common_slices L p hp.basic (![r, r + u, r + v]) hL hH
      hh hh1 hb hbβ hβg σ hσ hcover (ENNReal.ofReal δ)
  have hθμ : θ ≤ p.μ k := hθ.trans (hσ.trans (hp.basic k).2.2.2.2.1)
  have hbase : ∀ᵐ ω ∂θ, ω ∈ p.baseGood k :=
    (Basic.ae_baseGood p hp.basic k).filter_mono (ae_mono hθμ)
  have hcost : ENNReal.ofReal δ *
      ((Fintype.card (Fin 3) : ℝ≥0∞) * ENNReal.ofReal (240 * H ^ 3)) =
      ENNReal.ofReal (720 * δ * H ^ 3) := by
    simp only [Fintype.card_fin]
    rw [← ENNReal.ofReal_natCast 3,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg 3),
      ← ENNReal.ofReal_mul hδ.le]
    congr 1
    ring
  refine ⟨θ, hθ, hmass.trans_eq (congrArg (fun z => θ univ + z) hcost), ?_⟩
  have hall : ∀ᵐ ω ∂θ, ∀ a : Fin 3, ∃ e ∈ S, e.1.1 = a ∧
      ω ∈ sliceEvent menus (ProjectedLayer.familyEvent L) (p.domainCode k h g b) e :=
    ae_all_iff.mpr hretained
  filter_upwards [hall] with ω hω
  intro a i hi
  obtain ⟨⟨⟨a', j⟩, D⟩, heS, ha, heω⟩ := hω a
  dsimp only at ha
  subst a'
  have hj : ω.1 ∈ (L a).C j := heω.1.1
  have hij : j = i := by
    by_contra hne
    exact Set.disjoint_left.mp ((hL a).2.2.2.2.1 j i hne) hj hi
  subst i
  have hcode : p.shortDomainCode k r ω = D.val := heω.2
  have hsub : sliceEvent menus (ProjectedLayer.familyEvent L) (p.domainCode k h g b)
      ⟨⟨a, j⟩, D⟩ ≤ᵐ[θ] p.witnessSet k r (L a) j D.val := by
    filter_upwards [hbase] with z hz hze
    exact ⟨hz, hze.1.1, hze.2⟩
  have hf := (hfloor ⟨⟨a, j⟩, D⟩ heS).trans (measure_mono_ae hsub)
  change ENNReal.ofReal _ * _ ≤ θ (p.witnessSet k r (L a) j (p.shortDomainCode k r ω))
  rw [hcode]
  convert hf using 1
  dsimp only [ProjectedLayer.familyReference, ProjectedLayer.unscaledWeight]
  have hweight : δ * (h * p.N k ^ (-m) * b *
      (p.N k ^ (-![r, r + u, r + v] a)) ^ p.d) =
      δ * ((h * b) * (p.N k ^ (-m) * (p.N k ^ (-![r, r + u, r + v] a)) ^ p.d)) := by ring
  change ENNReal.ofReal (δ * (h * p.N k ^ (-m) * b *
      (p.N k ^ (-![r, r + u, r + v] a)) ^ p.d)) * _ = _
  rw [hweight, ENNReal.ofReal_mul hδ.le,
    ENNReal.ofReal_mul (mul_nonneg hh.le hb.le)]
  simp only [mul_assoc]

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
