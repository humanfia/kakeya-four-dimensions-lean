import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.ScalarCaps

/-!
# The pruned set and a dense candidate label

With the chosen scales, the four prunings lose at most `N^(-εL)/2` of `ρs`; some candidate
label then keeps `N^(-εL)/2` of its reference weight `q_c ν(A)`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

namespace CoreData

variable (D : CoreData α)

/-- Natural coefficient bound of the slice laws. -/
def Bnat (C₀ : ℝ) : ℝ := C₀ * D.N ^ D.εL * (D.N ^ D.εL) ^ 2 / D.Dw ^ 2

/-- Count cell exponent. -/
def r3 (σ : ℝ) : ℝ := -Real.logb D.N (σ * D.fc.q)

/-- Hidden cell width of the third pruning. -/
def W3 (K₁ C₀ σ : ℝ) : ℝ :=
  D.cellW0 σ + (2 * (D.N ^ D.εL * D.a₁) + D.crossLip D.M D.Dw K₁ (D.Bnat C₀) * D.cellδ2 σ +
    9 * D.Bnat C₀ * (2 * D.N ^ (-D.r3 σ)) * (1 + D.K + D.K ^ 2))

/-- The kept set of the first three prunings. -/
def S3 (K₁ C₀ σ : ℝ) : Set (α × ℝ) := D.G3 D.M D.Dw K₁ (D.r3 σ) (D.cellδ2 σ) (D.W3 K₁ C₀ σ)

/-- The final kept set. -/
def S4 (K₁ C₀ σ at' : ℝ) : Set (α × ℝ) := D.G4 (D.S3 K₁ C₀ σ) σ at' K₁

end CoreData

theorem N_r3 (D : CoreData α) (H : CoreHyp D) {σ : ℝ} (hσ : 0 < σ) :
    D.N ^ (-D.r3 σ) = σ * D.fc.q := by
  have hN : 1 < D.N := by linarith [H.N2]
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  unfold CoreData.r3
  rw [neg_neg, Real.rpow_logb (by linarith) hN.ne' (mul_pos hσ hqc)]

theorem S3_subset_G0 (D : CoreData α) (K₁ C₀ σ : ℝ) : D.S3 K₁ C₀ σ ⊆ D.G0 := fun x hx =>
  G1_subset D _ _ _ (G2_subset D _ _ _ (G3_subset D _ _ _ _ _ _ hx))

theorem measurableSet_S3 (D : CoreData α) (H : CoreHyp D) (K₁ C₀ σ : ℝ) :
    MeasurableSet (D.S3 K₁ C₀ σ) := measurableSet_G3 D H _ _ _ _ _ _

theorem measurableSet_S4 (D : CoreData α) (H : CoreHyp D) (K₁ C₀ σ at' : ℝ) :
    MeasurableSet (D.S4 K₁ C₀ σ at') := measurableSet_G4 D H (measurableSet_S3 D H K₁ C₀ σ) _ _ _

theorem S4_subset_G0 (D : CoreData α) (K₁ C₀ σ at' : ℝ) : D.S4 K₁ C₀ σ at' ⊆ D.G0 :=
  fun x hx => S3_subset_G0 D K₁ C₀ σ (G4_subset D _ _ _ _ hx)

/-- The four prunings keep half of the mass. -/
theorem S4_mass (D : CoreData α) (H : CoreHyp D) {K₁ C₀ σ at' : ℝ} (hK₁ : 1 ≤ K₁)
    (hok : CrossOK D D.M D.Dw K₁ (D.Bnat C₀)) (hσ : 0 < σ) (hat : 0 < at')
    (hχq : D.N ^ (-D.M) ≤ D.f₀.q * D.N ^ (-D.κ * D.s₀))
    (hDwq : D.Dw ≤ D.K * D.f₀.q * D.N ^ (-D.κ * D.s₀)) (hg1 : D.N ^ (-D.κ * D.s₀) ≤ 1)
    (hχD : D.N ^ (-D.M) ≤ D.Dw) (hχ1 : D.N ^ (-D.M) ≤ 1)
    (hh3χ : σ * D.fc.q ≤ D.N ^ (-D.M)) (hh3D : σ * D.fc.q ≤ D.Dw) (hb3D : D.cellδ2 σ ≤ D.Dw)
    (hh31 : σ * D.fc.q ≤ 1) (hb3pos : 0 < D.cellδ2 σ) (hW3pos : 0 < D.W3 K₁ C₀ σ)
    (hqe1 : D.fe.q / D.fc.q ≤ σ) (hqe2 : 3 * D.K * D.fe.q / D.fc.q ≤ σ)
    (hds : D.deepSpread ≤ at')
    (hloss : (810 * D.K ^ 4 + 4 * (594 * (D.N ^ D.εL) ^ 2 * D.N ^ D.εL) + 27) / K₁ ≤
      D.N ^ (-D.εL) / 2) :
    ENNReal.ofReal (D.N ^ (-D.εL) / 2) ≤ D.ρs (D.S4 K₁ C₀ σ at') := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hK₁0 : 0 < K₁ := by linarith
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  have hE0 : 0 ≤ D.N ^ D.εL := Real.rpow_nonneg hN0.le _
  have hDw : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
  have hχ0 : 0 < D.N ^ (-D.M) := Real.rpow_pos_of_pos hN0 _
  set G1 := D.G1 (D.N ^ (-D.M)) D.Dw K₁
  set G2 := D.G2 (D.N ^ (-D.M)) D.Dw K₁
  set G3 := D.S3 K₁ C₀ σ
  set G4 := D.S4 K₁ C₀ σ at'
  -- the four losses
  have L1 : D.ρs (D.G0 \ G1) ≤ ENNReal.ofReal (810 * D.K ^ 4 / K₁) := by
    refine (G1_loss D _ _ _).trans ?_
    rw [ENNReal.ofReal_div_of_pos hK₁0]
    gcongr
    exact R1_tsum_le D H hχ0 hDw hχq hDwq hg1
  have L2 : D.ρs (G1 \ G2) ≤
      ENNReal.ofReal (594 * (D.N ^ D.εL) ^ 2 * D.N ^ D.εL / K₁) := by
    refine (G2_loss D _ _ _).trans ?_
    rw [ENNReal.ofReal_div_of_pos hK₁0, ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact R2_tsum_le D H hχ0 hDw hok.εL0 le_rfl hχD le_rfl hχ1
  have hh3 : D.N ^ (-D.r3 σ) = σ * D.fc.q := N_r3 D H hσ
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have L3 : D.ρs (G2 \ G3) ≤
      ENNReal.ofReal (3 * (594 * (D.N ^ D.εL) ^ 2 * D.N ^ D.εL) / K₁) := by
    refine (G3_loss D _ _ _ _ _ _).trans ?_
    rw [ENNReal.ofReal_div_of_pos hK₁0]
    gcongr
    have hWsl : 2 * (D.N ^ D.εL * D.a₁) + D.crossLip D.M D.Dw K₁ (D.Bnat C₀) * D.cellδ2 σ +
        9 * D.Bnat C₀ * (2 * D.N ^ (-D.r3 σ)) * (1 + D.K + D.K ^ 2) ≤ D.W3 K₁ C₀ σ := by
      unfold CoreData.W3
      have : 0 ≤ D.cellW0 σ := by
        unfold CoreData.cellW0
        have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
        positivity
      linarith
    have h3 := R3_tsum_le D H hok hb3pos hW3pos (by rw [hh3]; exact hh3χ) hb3D hWsl
    have h2 := R2_tsum_le D H (hc := D.N ^ (-D.r3 σ)) (Hx := D.cellδ2 σ) (by rw [hh3]; positivity)
      hb3pos hok.εL0 (by rw [hh3]; exact hh3χ) (by rw [hh3]; exact hh3D) hb3D
      (by rw [hh3]; exact hh31)
    refine h3.trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_mul (by positivity)]
    gcongr
  have L4 : D.ρs (G3 \ G4) ≤ ENNReal.ofReal (27 / K₁) := by
    refine (G4_loss D _ _ _ _).trans ?_
    rw [ENNReal.ofReal_div_of_pos hK₁0]
    gcongr
    rw [ENNReal.ofReal_ofNat]
    exact R4_tsum_le D H (S3_subset_G0 D K₁ C₀ σ) hσ hat hqe1 hqe2 hds
  -- assembling
  have hsub : D.G0 ⊆ G4 ∪ (D.G0 \ G1) ∪ (G1 \ G2) ∪ (G2 \ G3) ∪ (G3 \ G4) := by
    intro x hx
    by_cases h4 : x ∈ G4
    · exact Or.inl (Or.inl (Or.inl (Or.inl h4)))
    by_cases h1 : x ∈ G1
    · by_cases h2 : x ∈ G2
      · by_cases h3 : x ∈ G3
        · exact Or.inr ⟨h3, h4⟩
        · exact Or.inl (Or.inr ⟨h2, h3⟩)
      · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hx, h1⟩)))
  have hG0 : D.ρs univ ≤ D.ρs D.G0 := by
    have hnull : D.ρs D.G0ᶜ = 0 := by
      have := ae_G0 D H; rw [ae_iff] at this; exact this
    calc D.ρs univ ≤ D.ρs D.G0 + D.ρs D.G0ᶜ := by
          rw [← union_compl_self D.G0]; exact measure_union_le _ _
      _ = D.ρs D.G0 := by rw [hnull, add_zero]
  have htot : ENNReal.ofReal (D.N ^ (-D.εL)) ≤ D.ρs G4 + ENNReal.ofReal (D.N ^ (-D.εL) / 2) := by
    calc ENNReal.ofReal (D.N ^ (-D.εL)) ≤ D.ρs univ := H.ρsmass
      _ ≤ D.ρs D.G0 := hG0
      _ ≤ D.ρs (G4 ∪ (D.G0 \ G1) ∪ (G1 \ G2) ∪ (G2 \ G3) ∪ (G3 \ G4)) := measure_mono hsub
      _ ≤ D.ρs G4 + D.ρs (D.G0 \ G1) + D.ρs (G1 \ G2) + D.ρs (G2 \ G3) + D.ρs (G3 \ G4) := by
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          exact measure_union_le _ _
      _ ≤ D.ρs G4 + ENNReal.ofReal (810 * D.K ^ 4 / K₁) +
            ENNReal.ofReal (594 * (D.N ^ D.εL) ^ 2 * D.N ^ D.εL / K₁) +
            ENNReal.ofReal (3 * (594 * (D.N ^ D.εL) ^ 2 * D.N ^ D.εL) / K₁) +
            ENNReal.ofReal (27 / K₁) := by
          gcongr
      _ = D.ρs G4 + ENNReal.ofReal ((810 * D.K ^ 4 + 4 * (594 * (D.N ^ D.εL) ^ 2 * D.N ^ D.εL) +
            27) / K₁) := by
          rw [add_assoc, add_assoc, add_assoc,
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2; ring
      _ ≤ D.ρs G4 + ENNReal.ofReal (D.N ^ (-D.εL) / 2) := by gcongr
  have hhalf : ENNReal.ofReal (D.N ^ (-D.εL)) = ENNReal.ofReal (D.N ^ (-D.εL) / 2) +
      ENNReal.ofReal (D.N ^ (-D.εL) / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  rw [hhalf] at htot
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp htot

/-- Some candidate label keeps half of its reference weight. -/
theorem exists_dense_label (D : CoreData α) (H : CoreHyp D) {K₁ C₀ σ at' : ℝ}
    (hmass : ENNReal.ofReal (D.N ^ (-D.εL) / 2) ≤ D.ρs (D.S4 K₁ C₀ σ at')) :
    ∃ Q : Fin D.fc.n, ENNReal.ofReal (D.N ^ (-D.εL) / 2) * (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q)) ≤
      D.ρs (D.S4 K₁ C₀ σ at' ∩ (D.fc.B Q ×ˢ D.fc.I Q)) := by
  classical
  haveI := H.νprob
  have hN0 : 0 < D.N := by linarith [H.N2]
  by_contra hcon
  push Not at hcon
  have hcov : D.S4 K₁ C₀ σ at' ⊆ ⋃ Q : Fin D.fc.n, D.S4 K₁ C₀ σ at' ∩ (D.fc.B Q ×ˢ D.fc.I Q) := by
    intro x hx
    obtain ⟨Q, hB, hI⟩ := (S4_subset_G0 D K₁ C₀ σ at' hx).2.2.2.2.2.1
    exact mem_iUnion.mpr ⟨Q, hx, hB, hI⟩
  have hpos : 0 < ENNReal.ofReal (D.N ^ (-D.εL) / 2) := by
    rw [ENNReal.ofReal_pos]; have := Real.rpow_pos_of_pos hN0 (-D.εL); linarith
  have hlt : D.ρs (D.S4 K₁ C₀ σ at') < ENNReal.ofReal (D.N ^ (-D.εL) / 2) := by
    rcases isEmpty_or_nonempty (Fin D.fc.n) with hE | hNe
    · have : D.S4 K₁ C₀ σ at' ⊆ ∅ := by
        intro x hx
        obtain ⟨Q, -, -⟩ := (S4_subset_G0 D K₁ C₀ σ at' hx).2.2.2.2.2.1
        exact (IsEmpty.false Q).elim
      rw [Set.subset_empty_iff.mp this, measure_empty]; exact hpos
    · calc D.ρs (D.S4 K₁ C₀ σ at')
          ≤ ∑ Q : Fin D.fc.n, D.ρs (D.S4 K₁ C₀ σ at' ∩ (D.fc.B Q ×ˢ D.fc.I Q)) :=
            (measure_mono hcov).trans (measure_iUnion_fintype_le _ _)
        _ < ∑ Q : Fin D.fc.n, ENNReal.ofReal (D.N ^ (-D.εL) / 2) *
              (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q)) :=
            ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun Q _ => hcon Q)
        _ = ENNReal.ofReal (D.N ^ (-D.εL) / 2) *
              ∑ Q : Fin D.fc.n, ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q) := by
            rw [Finset.mul_sum]
        _ ≤ ENNReal.ofReal (D.N ^ (-D.εL) / 2) * 1 := by
            gcongr
            exact label_weights_le_one D.ν D.fc H.fcgood.measA H.fcgood.disj
        _ = _ := mul_one _
  exact absurd hmass (not_le.mpr hlt)

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
