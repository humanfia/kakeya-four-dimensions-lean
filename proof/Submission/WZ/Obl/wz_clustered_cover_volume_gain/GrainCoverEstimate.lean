-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.GrainCoverEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ConfinedFamily
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DenseGrains
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainData
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SelectedDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ThickGrainDensity

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory Metric
open scoped ENNReal

/-- The geometric medium estimate with all numerical budgets explicit.
Its two density alternatives are uniform across every selected coarse box. -/
theorem grain_cover_density_or_medium {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ Cb η d₀ : ℝ, 0 < Cb ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
    ∀ d δ h ρ : ℝ, 0 < d → d ≤ d₀ → 0 < δ → 0 < ρ → ρ ≤ 1 →
    ∀ (n N J : ℕ) (x v : Fin n → V) (Y Z : Fin n → Set V) (S : Finset (Fin n))
      (y w : Fin N → V) (f : Fin n → Fin N),
    A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y → C δ h n x v Y S Z ρ N y w f →
    ∀ Gd : GrainData δ h ρ n N S Z y w f,
    ∀ (U : Finset (Fin N)) (g : Fin N → Fin J) (z₀ : Fin J → V)
      (e₀ : Fin J → V ≃ₗᵢ[ℝ] V) (a₀ b₀ s D R lam t loss Cm : ℝ) (A : ℕ) (X : Set V),
    ρ ≤ a₀ → a₀ ≤ b₀ → 0 < s → s ≤ 1 → 1 ≤ A →
    (Gd.L : ℝ) ≤ d ^ (-100 : ℝ) →
    (Gd.a ≤ 2 * R → Gd.a ≤ s * ρ * Gd.c) → s * ρ * Gd.c ≤ A * Gd.a →
    1 ≤ δ ^ (-h) → 0 < D → 1536 * d ^ η ≤ D / 8 → d ≤ Gd.a / 20000 →
    256 * d ^ 2 ≤ Gd.a * ρ / (800000000 * (min 1 b₀) ^ 2 * s * Gd.c) →
    0 < R → (s = 1 ∨ R ≤ (s / 2) * ρ * Gd.c) → 0 ≤ lam → 0 < t →
    D ≤ t / 4 * δ ^ h →
    O (δ ^ loss) ≤ O (t / 128) * O (δ ^ h) →
    Cb * d ^ (-ε) * (D / 8)⁻¹ *
      ((((128 * A ^ 2 + 1) ^ 6 : ℕ) : ℝ) * δ ^ (-h)) ^ (1 + σ / 2) *
      (Gd.a * ρ / (800000000 * (min 1 b₀) ^ 2 * s * Gd.c)) ^ (-(ω + σ) / 2) ≤
      Cm * δ ^ (-loss) * (ρ / b₀) ^ (-ω - σ) →
    MeasurableSet X → X ⊆ ⋃ i, Y i →
    (∀ p ∈ X, volume ((⋃ i, Y i) ∩ ball p R) ≤ O (2 * lam * R ^ 3)) →
    O t * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i ∩ selectedCut U X (f i)) →
    (∀ k ∈ U, T ρ (y k) (w k) ⊆ P a₀ b₀ 8 (z₀ (g k)) (e₀ (g k))) →
    D ≤ 1024 * lam ∨ confinementDensity Gd.a ρ Gd.c D s ≤ 92160 * lam ∨
      ∃ W : Fin n → Set V, MR σ ω δ loss ρ b₀ Cm n N J Y Z W S U f g := by
  intro ε hε
  obtain ⟨Cb, η, d₀, hCb, hη, hd₀, hd₀small, Hbody⟩ :=
    confined_family_density_or_refinement hσ hσhalf hω (tubeEstimate_of_E hE) ε hε
  refine ⟨Cb, η, d₀, hCb, hη, hd₀, hd₀small, ?_⟩
  intro d δ h ρ hd hdd hδ hρ hρ1 n N J x v Y Z S y w f hA hC Gd U g z₀ e₀ a₀ b₀
    s D R lam t loss Cm A X hρa₀ ha₀b₀ hs hs1 hAcount hcard hthin hAs hm hD hDη
    hda hscale hR hRs hlam ht hbudget hmassbudget hcountbudget hXm hXU hupper hkeep hcover
  have ha : 0 < Gd.a := hδ.trans_le Gd.short
  have hc : 0 < Gd.c := ha.trans_le (Gd.middle.trans Gd.long)
  have hZm := fun i => (hC.1 i).1
  have hZsupport := fun i => (hC.1 i).2.2
  have hZY := fun i => (hC.1 i).2.1
  have hYball : ∀ i, Y i ⊆ ball 0 1 := fun i => (hA.2.1 i).2.2.2.trans (hA.2.1 i).2.1
  have hZmass := frozen_shading_mass_positive hδ hA hC
  obtain ⟨mf, hmf, hlevel⟩ := Gd.fine_positive hZsupport hZmass
  have hcutkeep : O t * ∑ i, volume (Z i) ≤ ∑ i, volume (Z i ∩ selectedCut U X (f i)) :=
    (mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => measure_mono (hZY i))).trans hkeep
  have hcost : (∑ j, O D * volume (P Gd.a (ρ * Gd.c) Gd.c (Gd.z j) (Gd.e j))) ≤
      O (t / 4) * ∑ j, volume (Gd.H j) := by
    calc
      _ = O (D * Gd.L * Gd.a * (ρ * Gd.c) * Gd.c) := by
        simp only [frozen_prism_volume ha.le (mul_pos hρ hc).le hc.le,
          ← ENNReal.ofReal_mul hD.le, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg Gd.L)]
        congr 1
        ring
      _ ≤ O ((t / 4 * δ ^ h) * Gd.L * Gd.a * (ρ * Gd.c) * Gd.c) := by
        apply ENNReal.ofReal_le_ofReal
        gcongr
      _ = O (t / 4) * O (δ ^ h * Gd.L * Gd.a * (ρ * Gd.c) * Gd.c) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ t / 4)]
        congr 1
        ring
      _ ≤ _ := mul_le_mul' le_rfl Gd.density
  obtain ⟨H₁, hH₁, hH₁mass, hH₁dense⟩ := common_cut_dense_grains f Gd.γ Z Gd.H
    (fun j => P Gd.a (ρ * Gd.c) Gd.c (Gd.z j) (Gd.e j)) (selectedCut U X) hmf ht.le
    hZm Gd.measurable (selectedCut_measurable U hXm) (Gd.mass_finite hZY hYball)
    Gd.disjoint (Gd.fiber_eq hZsupport) hlevel hcutkeep hcost
  have hH₁prism (j) : H₁ j ⊆ P Gd.a (ρ * Gd.c) Gd.c (Gd.z j) (Gd.e j) :=
    (hH₁ j).2.trans (inter_subset_left.trans (Gd.shading j))
  have hH₁X (j) : H₁ j ⊆ X := (hH₁ j).2.trans
    (inter_subset_right.trans (selectedCut_subset U X (Gd.γ j)))
  have hH₁selected (j) (hj : H₁ j ≠ ∅) : Gd.γ j ∈ U := by
    by_contra hh
    apply hj
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hh' := ((hH₁ j).2 hp).2
    simpa only [selectedCut, if_neg hh, mem_empty_iff_false] using hh'
  by_cases hthick : 2 * R ≤ Gd.a
  · have hpositive : 0 < ∑ j, volume (H₁ j) :=
      (by have := Gd.mass_positive hZsupport hZmass; positivity :
        0 < O (t / 4) * ∑ j, volume (Gd.H j)).trans_le hH₁mass
    have hex : ∃ j, H₁ j ≠ ∅ := by
      by_contra hh
      push_neg at hh
      simp only [hh, measure_empty, Finset.sum_const_zero] at hpositive
      exact lt_irrefl _ hpositive
    obtain ⟨j, hj⟩ := hex
    have hden := thick_grain_forces_ball_density ha Gd.middle Gd.long hR (by linarith)
      hD.le (by positivity : 0 ≤ 2 * lam) (Gd.z j) (Gd.e j) (H₁ j) (⋃ i, Y i)
      ((hH₁X j).trans hXU) (hH₁prism j) (hH₁dense j hj)
      (fun p hp => hupper p (hH₁X j hp))
    exact Or.inl (by linarith)
  right
  rcases Hbody d hd hdd Gd.L N J A hAcount hcard ρ Gd.a Gd.c s (δ ^ (-h)) D R (2 * lam)
    a₀ b₀ hρ hρ1 hρa₀ ha₀b₀ ha Gd.middle hc Gd.length hs hs1 (hthin (le_of_not_ge hthick))
    hAs hm hD hDη hda hscale hR hRs (by positivity) Gd.z Gd.e H₁ Gd.γ y w g z₀ e₀ X
    (⋃ i, Y i) (fun j => (hH₁ j).1) hH₁prism hH₁X hXU (iUnion_subset hYball)
    hH₁dense (fun j _ => hC.2.2.1 (Gd.γ j)) (fun j _ => Gd.alignment j)
    (fun j hj => hcover (Gd.γ j) (hH₁selected j hj)) hupper Gd.localCount with hden | hgood
  · exact Or.inl (by linarith)
  right
  obtain ⟨H₂, hH₂, hH₂mass, hH₂count⟩ := hgood
  have hmass : O (t / 64) * ∑ j, volume (Gd.H j) ≤ ∑ j, volume (H₂ j) := by
    calc
      _ = (1 / 16 : ℝ≥0∞) * (O (t / 4) * ∑ j, volume (Gd.H j)) := by
        have he : (1 / 16 : ℝ≥0∞) = O (1 / 16 : ℝ) := by norm_num [O, ENNReal.ofReal_div_of_pos]
        rw [he, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 16)]
        congr 2
        ring
      _ ≤ (1 / 16 : ℝ≥0∞) * ∑ j, volume (H₁ j) := mul_le_mul' le_rfl hH₁mass
      _ ≤ _ := hH₂mass
  apply medium_certificate_of_grain_refinement hC Gd.fine (by positivity : 0 ≤ t / 64)
    (by simpa only [show t / 64 / 2 = t / 128 by ring] using hmassbudget) Gd.measurable (fun j => (hH₂ j).1)
    (fun j => (hH₂ j).2.trans ((hH₁ j).2.trans inter_subset_left)) Gd.disjoint Gd.fibers hmass
  · intro j hj
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have he : H₁ j ≠ ∅ := Set.Nonempty.ne_empty ⟨p, (hH₂ j).2 hp⟩
    exact hj (hH₁selected j he)
  · intro p k
    apply le_trans _ hcountbudget
    apply le_trans _ (hH₂count k p)
    rw [fiberBodyCount_eq_ncard]
    apply Nat.cast_le.mpr
    exact Set.ncard_le_ncard (fun j hj => ⟨hj.2.1, hj.2.2⟩) (Set.toFinite _)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
