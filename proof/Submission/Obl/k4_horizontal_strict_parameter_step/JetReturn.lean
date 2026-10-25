import Submission.Obl.k4_horizontal_strict_parameter_step.JetFamilies
import Submission.Obl.k4_horizontal_strict_parameter_step.FirstJet.Statement

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/JetReturn.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

noncomputable section

/-- Returning one normalized first-jet cover to its original full-time chart.
Unused large menu entries are discarded before the coefficient restoration. -/
theorem firstJet_cover_to_chart_family {α : Type} [MeasurableSpace α]
    (ν : Measure α) {E : Set (α × ℝ)} {A : Set α} (hA : MeasurableSet A)
    (hEA : ∀ p ∈ E, p.1 ∈ A)
    {r : α → Fin 2 → ℝ} {p q : α → ℝ} (hr : Measurable r)
    (hp : Measurable p) (hq : Measurable q)
    (y : α → Fin 2 → ℝ) (β γ : α → ℝ) (F : ℝ → Fin 2 → ℝ)
    (h : Fin 6 → ℝ) {a D p₀ q₀ K M₀ d N ε w : ℝ}
    (ha : 0 ≤ a) (hD : 0 < D) (hK : 0 ≤ K) (hM₀ : 0 ≤ M₀)
    (hN : 0 < N) (hw : 0 < w)
    (hcoords : ∀ l ∈ A, y l 0 = (p l - p₀) / D ∧ y l 1 = (q l - q₀) / D ∧
      β l = r l 0 ∧ γ l = r l 1)
    (hy : ∀ l ∈ A, |(p l - p₀) / D| ≤ 1 ∧ |(q l - q₀) / D| ≤ 1)
    (hrbound : ∀ l ∈ A, (∀ t ∈ Icc (0 : ℝ) 1, |r l 0 + t * r l 1| ≤ K) ∧ |r l 1| ≤ 2 * K)
    (hF : ∀ t i, |F t i| ≤ M₀)
    (hbase : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
      |predictor h t p q| ≤ K)
    (hcover : FirstJet.Cover ν y β γ E F d N ε w) :
    ∃ (n : ℕ) (B : Fin n → Set α) (h' : Fin n → Fin 6 → ℝ),
      (∀ i, MeasurableSet (B i)) ∧ (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i, B i ⊆ A) ∧ (n : ℝ) ≤ N ^ ε * w ^ (-d) ∧
      ENNReal.ofReal (N ^ (-ε)) ≤ (ν.prod volume) (E ∩ (⋃ i, B i) ×ˢ univ) ∧
      (∀ i, ∀ l ∈ B i, ∀ t ∈ Icc (0 : ℝ) 1,
        |predictor h t (p l) (q l) + a * (r l 0 + t * r l 1) -
          predictor (h' i) t (p l) (q l)| ≤ 2 * a * w) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
        |predictor (h' i) t p q| ≤ K + 6 * a * (3 * (K + M₀ + N ^ ε + w + 1))) := by
  classical
  obtain ⟨t₀, ht₀, R, hR, L, hL, hmass, P, hPcard, hmenu⟩ := hcover
  let C := L ∩ A
  let M := 3 * (K + M₀ + N ^ ε + w + 1)
  have hpow : 0 < N ^ ε := Real.rpow_pos_of_pos hN _
  have hFM : M₀ ≤ M := by dsimp [M]; nlinarith
  have hRM : N ^ ε ≤ M := by dsimp [M]; nlinarith
  let code := jetCode r p q D p₀ q₀ t₀ w (F t₀) R
  have hcodeP : ∀ l ∈ C, code l ∈ P := by
    intro l hl
    obtain ⟨hy0, hy1, hβ, hγ⟩ := hcoords l hl.2
    have hv : FirstJet.scal y β γ F l t₀ =
        jetCoordinates r p q D p₀ q₀ t₀ (F t₀) R l 0 := by
      simp only [FirstJet.scal, FirstJet.xbar, jetCoordinates, Matrix.cons_val_zero]
      rw [hy0, hy1, hβ, hγ]
      ring
    have hs : γ l - (R 0 * y l 0 + R 1 * y l 1) =
        jetCoordinates r p q D p₀ q₀ t₀ (F t₀) R l 1 := by
      simp only [jetCoordinates, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hy0, hy1, hγ]
      ring
    have hm := hmenu l hl.1
    rw [hv, hs] at hm
    exact hm
  have hprod (v z B : ℝ) (hv : |v| ≤ B) (hz : |z| ≤ 1) : |v * z| ≤ B := by
    rw [abs_mul]
    have hB : 0 ≤ B := (abs_nonneg _).trans hv
    exact (mul_le_mul hv hz (abs_nonneg _) hB).trans_eq (mul_one B)
  have hfloor (x B : ℝ) (hx : |x| ≤ B) : |w * (⌊x / w⌋ : ℝ)| ≤ B + w := by
    have herr := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hw x
    calc
      _ = |x - (x - w * (⌊x / w⌋ : ℝ))| := by congr 1; ring
      _ ≤ |x| + |x - w * (⌊x / w⌋ : ℝ)| := abs_sub _ _
      _ ≤ _ := add_le_add hx herr
  have hcenters : ∀ l ∈ C, |w * ((code l).1 : ℝ)| ≤ M ∧ |w * ((code l).2 : ℝ)| ≤ M := by
    intro l hl
    have hy' := hy l hl.2
    have hr' := hrbound l hl.2
    have hv : |jetCoordinates r p q D p₀ q₀ t₀ (F t₀) R l 0| ≤ K + 2 * M₀ := by
      change |r l 0 + t₀ * r l 1 - F t₀ 0 * ((p l - p₀) / D) - F t₀ 1 * ((q l - q₀) / D)| ≤ _
      exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
        (by linarith [hr'.1 t₀ ht₀, hprod _ _ _ (hF t₀ 0) hy'.1, hprod _ _ _ (hF t₀ 1) hy'.2])
    have hs : |jetCoordinates r p q D p₀ q₀ t₀ (F t₀) R l 1| ≤ 2 * K + 2 * N ^ ε := by
      change |r l 1 - R 0 * ((p l - p₀) / D) - R 1 * ((q l - q₀) / D)| ≤ _
      exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
        (by linarith [hr'.2, hprod _ _ _ (hR 0) hy'.1, hprod _ _ _ (hR 1) hy'.2])
    exact ⟨(hfloor _ _ hv).trans (by dsimp [M]; nlinarith),
      (hfloor _ _ hs).trans (by dsimp [M]; nlinarith)⟩
  let P' := P.filter fun z => |w * (z.1 : ℝ)| ≤ M ∧ |w * (z.2 : ℝ)| ≤ M
  let menu : Fin P'.card → ℤ × ℤ := fun i => (P'.equivFin.symm i).val
  have hmBound : ∀ i, |w * ((menu i).1 : ℝ)| ≤ M ∧ |w * ((menu i).2 : ℝ)| ≤ M := by
    intro i
    exact (Finset.mem_filter.mp (P'.equivFin.symm i).property).2
  have hmCover : ∀ l ∈ C, ∃ i, code l = menu i := by
    intro l hl
    have hmem : code l ∈ P' := Finset.mem_filter.mpr ⟨hcodeP l hl, hcenters l hl⟩
    refine ⟨P'.equivFin ⟨code l, hmem⟩, ?_⟩
    simp only [menu, Equiv.symm_apply_apply]
  obtain ⟨B, h', hBm, hBd, hBC, hBU, hfit, hnorm⟩ :=
    jet_cover_to_family (hL.inter hA) hr hp hq h a D p₀ q₀ t₀ w K M (F t₀) R menu ha hD hw ht₀
      hmCover hbase hmBound (fun i => (hF t₀ i).trans hFM) (fun i => (hR i).trans hRM)
  refine ⟨P'.card, B, h', hBm, hBd, (fun i l hl => (hBC i hl).2), ?_, ?_, hfit, hnorm⟩
  · exact (show (P'.card : ℝ) ≤ P.card by exact_mod_cast Finset.card_filter_le _ _).trans hPcard
  · rw [hBU]
    have heq : E ∩ C ×ˢ univ = E ∩ L ×ˢ univ := by
      ext p
      constructor
      · rintro ⟨hp, ⟨hl, ha⟩, ht⟩
        exact ⟨hp, hl, ht⟩
      · rintro ⟨hp, hl, ht⟩
        exact ⟨hp, ⟨hl, hEA p hp⟩, ht⟩
    rw [heq]
    exact hmass

end

end Submission.Obl.k4_horizontal_strict_parameter_step
