import Submission.Obl.k4_horizontal_wide_interval_return.Core.LayerCompare

/-!
# From small sheet gaps to agreement on the whole strip, and the good restriction

If the normalized sheets of a layer-0 piece and a layer-`h` piece of the same key differ by
less than `Mst` in every coefficient, their polynomials differ by at most `6 a Mst` on the whole
moving strip.  Removing the bad pairs of layers `1` and `2` from `ρ⋆` keeps all the datum's
properties, costs only the bad mass, and gives the agreement `ρ⋆`-almost everywhere.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return.Core

open MeasureTheory Set Filter
open Submission.Obl.k4_horizontal_wide_interval_return.MatchGML2D
open Submission.Obl.k4_horizontal_wide_interval_return.CompareSheets

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Small coefficient gap gives agreement on the whole strip. -/
theorem strip_agree_of_gap {G₀ Gh : MvPolynomial (Fin 2) ℝ} (h₀ : G₀.totalDegree ≤ 2)
    (hh : Gh.totalDegree ≤ 2) (κ : Fin 3 → ℤ) {χ D a Mst : ℝ} (hD : 0 < D) (ha : 0 < a)
    (hgap : ∀ k', |keySheet G₀ κ χ D a k' - keySheet Gh κ χ D a k'| ≤ Mst)
    {t w : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (-1 : ℝ) 1) :
    |MvPolynomial.eval (![t, (κ 2 : ℝ) * D - t * ((κ 1 : ℝ) * χ) + D * w] : Fin 2 → ℝ)
      (Gh - G₀)| ≤ a * (6 * Mst) := by
  set η : ℝ := (w + 2) / 4
  have hpt : (κ 2 : ℝ) * D - t * ((κ 1 : ℝ) * χ) + D * w =
      (κ 2 : ℝ) * D + t * -((κ 1 : ℝ) * χ) + D * (4 * η - 2) := by
    simp only [η]; ring
  have hval : ∀ G : MvPolynomial (Fin 2) ℝ, G.totalDegree ≤ 2 →
      MvPolynomial.eval (![t, (κ 2 : ℝ) * D - t * ((κ 1 : ℝ) * χ) + D * w] : Fin 2 → ℝ) G =
        a * quad2 (keySheet G κ χ D a) t η := by
    intro G hG
    rw [hpt, ← quad2_sheetCoeff hG, keySheet, quad2_smul, ← mul_assoc, mul_inv_cancel₀ ha.ne',
      one_mul]
  rw [map_sub, hval Gh hh, hval G₀ h₀, ← mul_sub, abs_mul, abs_of_pos ha]
  apply mul_le_mul_of_nonneg_left _ ha.le
  rw [quad2_sub]
  apply abs_quad2_le (fun k' => by rw [Pi.sub_apply, abs_sub_comm]; exact hgap k')
  · rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  · rw [abs_le]; simp only [η]; constructor <;> linarith [hw.1, hw.2]

namespace LayerDatum

variable {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}

/-- Restrict the dense measure of the datum to a set and relax its loss from `ε` to `ε₁ ≥ ε`. -/
def restrictTo (L : LayerDatum cfg k ε R χ D depth) {ε₁ : ℝ} (hε : ε ≤ ε₁)
    (hN : 1 ≤ cfg.N k) (hχ : 0 ≤ χ) (hD : 0 ≤ D) (S : Set (α × ℝ))
    (hmass : ENNReal.ofReal (cfg.N k ^ (-ε₁)) ≤ L.ρs S) : LayerDatum cfg k ε₁ R χ D depth where
  ρs := L.ρs.restrict S
  np := L.np
  C := L.C
  qp := L.qp
  G := L.G
  le_rho := Measure.restrict_le_self.trans L.le_rho
  mass := by rw [Measure.restrict_apply_univ]; exact hmass
  cover := ae_restrict_of_ae L.cover
  meas := L.meas
  disj := L.disj
  piece := by
    have hNε : cfg.N k ^ ε ≤ cfg.N k ^ ε₁ := Real.rpow_le_rpow_of_exponent_le hN hε
    have hN0 : 0 < cfg.N k := by linarith
    intro h i
    obtain ⟨hmem, hkey, hdeg, hcoef, hstrip, hfit, hfloor⟩ := L.piece h i
    refine ⟨fun l hl => ?_, hkey.trans hNε, hdeg, hcoef, fun t ht w hw => (hstrip t ht w hw).trans hNε,
      fun l hl t ht => ?_, ?_⟩
    · obtain ⟨a1, a2, a3, a4⟩ := hmem l hl
      exact ⟨a1, a2, a3, fun e => (a4 e).trans hNε⟩
    · obtain ⟨f1, f2⟩ := hfit l hl t ht
      refine ⟨f1.trans ?_, f2.trans ?_⟩
      · exact mul_le_mul_of_nonneg_right hNε hD
      · exact mul_le_mul_of_nonneg_right hNε (Real.rpow_nonneg hN0.le _)
    · refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) hfloor
      have hχD : 0 ≤ χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d :=
        mul_nonneg (mul_nonneg hχ hD) (Real.rpow_nonneg (Real.rpow_nonneg hN0.le _) _)
      exact div_le_div_of_nonneg_left hχD (Real.rpow_pos_of_pos hN0 _) hNε
  sum := by
    have hNε : cfg.N k ^ ε ≤ cfg.N k ^ ε₁ := Real.rpow_le_rpow_of_exponent_le hN hε
    intro h
    exact (L.sum h).trans (ENNReal.ofReal_le_ofReal hNε)

/-- The bad pairs of layer `h` at gap `Mst`. -/
def badSet (L : LayerDatum cfg k ε R χ D depth) (h : Fin 3) (Mst : ℝ) : Set (α × ℝ) :=
  ⋃ i : Fin (L.np 0), ⋃ j ∈ Finset.univ.filter
    (fun j => ∃ k', Mst ≤ |L.sheet 0 i k' - L.sheet h j k'|), (L.C 0 i ∩ L.C h j) ×ˢ univ

theorem measurableSet_badSet (L : LayerDatum cfg k ε R χ D depth) (h : Fin 3) (Mst : ℝ) :
    MeasurableSet (L.badSet h Mst) :=
  MeasurableSet.iUnion fun i => Finset.measurableSet_biUnion _ fun j _ =>
    ((L.meas 0 i).inter (L.meas h j)).prod MeasurableSet.univ

theorem badSet_le (L : LayerDatum cfg k ε R χ D depth) (h : Fin 3) (Mst : ℝ) :
    L.ρs (L.badSet h Mst) ≤ ∑ i, ∑ j ∈ Finset.univ.filter
      (fun j => ∃ k', Mst ≤ |L.sheet 0 i k' - L.sheet h j k'|), L.ρs ((L.C 0 i ∩ L.C h j) ×ˢ univ) :=
  (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => measure_biUnion_finset_le _ _)

/-- Outside the bad sets, layers `1` and `2` agree with layer `0` on the whole strip. -/
theorem agree_off_bad (L : LayerDatum cfg k ε R χ D depth) (hD : 0 < D)
    (ha : 0 < cfg.N k ^ (-depth 0)) {Mst : ℝ} {p : α × ℝ}
    (hp : p ∉ L.badSet 1 Mst ∪ L.badSet 2 Mst) :
    ∀ h : Fin 3, h ≠ 0 → ∀ (i₀ : Fin (L.np 0)) (ih : Fin (L.np h)),
      p.1 ∈ L.C 0 i₀ → p.1 ∈ L.C h ih → ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
        |MvPolynomial.eval (![t, (L.qp 0 i₀ 2 : ℝ) * D - t * ((L.qp 0 i₀ 1 : ℝ) * χ) + D * w] :
          Fin 2 → ℝ) (L.G h ih - L.G 0 i₀)| ≤ cfg.N k ^ (-depth 0) * (6 * Mst) := by
  intro h hh i₀ ih h0 hhp t ht w hw
  have hkey : L.qp h ih = L.qp 0 i₀ := by
    by_contra hne
    have := L.inter_empty_of_key_ne hne
    exact (this ▸ ⟨h0, hhp⟩ : p.1 ∈ (∅ : Set α))
  have hgap : ∀ k', |L.sheet 0 i₀ k' - L.sheet h ih k'| ≤ Mst := by
    intro k'
    by_contra hbig
    push_neg at hbig
    apply hp
    have hmem : p ∈ L.badSet h Mst := by
      refine mem_iUnion.mpr ⟨i₀, mem_iUnion₂.mpr ⟨ih, ?_, ⟨h0, hhp⟩, trivial⟩⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨k', hbig.le⟩
    have hh' : h = 1 ∨ h = 2 := by
      fin_cases h
      · exact absurd rfl hh
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hh' with rfl | rfl
    · exact Or.inl hmem
    · exact Or.inr hmem
  have hgap' : ∀ k', |keySheet (L.G 0 i₀) (L.qp 0 i₀) χ D (cfg.N k ^ (-depth 0)) k' -
      keySheet (L.G h ih) (L.qp 0 i₀) χ D (cfg.N k ^ (-depth 0)) k'| ≤ Mst := by
    intro k'
    have := hgap k'
    simp only [sheet] at this
    rw [hkey] at this
    exact this
  exact strip_agree_of_gap (L.degree 0 i₀) (L.degree h ih) (L.qp 0 i₀) hD ha hgap' ht hw

end LayerDatum

end

end Submission.Obl.k4_horizontal_wide_interval_return.Core
