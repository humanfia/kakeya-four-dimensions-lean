-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.HierarchyAnalysis.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyShadows
import Submission.WZ.Obl.wz_multiscale_finite_tower.IndexTransport

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridCell gridUnion)
open WangZahlLot.Obl.wz_flat_factored_improvement (gridHull)

/-- Density ratios retain the same reference set throughout the hierarchy. -/
structure HierarchyAnalysis {J : ℕ} (T : TubeHierarchy J) (E : Set Space) (d θ ρ : ℝ) where
  shading : ∀ j, Fin (T.layer j).card → Set Space
  density : ℕ → ℝ
  positive : ∀ j, j ≤ J → 0 < density j
  terminal : density J = 1
  measurable : ∀ j, j ≤ J → ∀ i, MeasurableSet (shading j i)
  containment : ∀ j, j ≤ J → ∀ i,
    shading j i ⊆ Tube (T.layer j).radius ((T.layer j).position i) ((T.layer j).direction i)
  mass : ∀ j, j ≤ J → ∀ i,
    ENNReal.ofReal (d ^ θ * (T.layer j).radius ^ 2) ≤ volume (shading j i)
  root : ENNReal.ofReal (d ^ θ * density 0) ≤ volume E
  transfer : ∀ j, j < J → ∀ k : Fin (T.layer j).card, ∀ m : ℕ,
    ∀ e : Fin m → Fin (T.layer (j + 1)).card, (∀ i, T.parent j (e i) = k) →
    ENNReal.ofReal (ρ * density (j + 1)) * volume (⋃ i, shading (j + 1) (e i)) ≤
      ENNReal.ofReal (256 * density j * (T.layer j).radius ^ 2)

noncomputable def terminalDensity (J : ℕ) (t : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j < J then t j else 1

lemma hierarchyShading_local_density {J : ℕ} (T : TubeHierarchy J)
    {Z : Fin (T.layer J).card → Set Space} {E : Set Space}
    (hE : MeasurableSet E) (hZE : ∀ i, Z i ⊆ E)
    (a t : ℕ → ℝ) (S : ℕ → Finset (Fin 3 → ℤ)) {j : ℕ}
    (ha : j < J → 0 < a j) (ht : j < J → 0 ≤ t j)
    (hclass : j < J → ∀ z ∈ S j, t j * (a j) ^ 3 ≤ volume.real (E ∩ gridCell (a j) z))
    (m : ℕ) (e : Fin m → Fin (T.layer j).card) :
    ENNReal.ofReal (terminalDensity J t j) * volume (⋃ i, hierarchyShading T Z a S j (e i)) ≤
      volume (E ∩ ⋃ i, hierarchyShading T Z a S j (e i)) := by
  by_cases hj : j < J
  · have he : (⋃ i, hierarchyShading T Z a S j (e i)) =
        gridHull (a j) (S j) (⋃ i, descendantUnion T Z j (e i)) := by
      simp only [hierarchyShading, if_pos hj]
      exact (gridHull_iUnion _ _ _).symm
    rw [he, terminalDensity, if_pos hj]
    exact gridHull_local_density (ha hj) (ht hj) (S j) hE (hclass hj) _
  · have hsub : (⋃ i, hierarchyShading T Z a S j (e i)) ⊆ E := by
      apply iUnion_subset
      intro i
      rw [hierarchyShading, if_neg hj]
      exact descendantUnion_subset T hZE j (e i)
    rw [terminalDensity, if_neg hj, ENNReal.ofReal_one, one_mul, inter_eq_right.mpr hsub]

theorem hierarchy_analysis_of_grids {d θ₀ θ g gap ρ lam : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ₀ g gap T) (hd : 0 < d) (hρ : 0 ≤ ρ)
    (hgap : d ^ gap ≤ 1 / 64) {E : Set Space} (hE : MeasurableSet E)
    {Z : Fin (T.layer J).card → Set Space}
    (hZm : ∀ i, MeasurableSet (Z i)) (hZE : ∀ i, Z i ⊆ E)
    (hZT : ∀ i, Z i ⊆ Tube d ((T.layer J).position i) ((T.layer J).direction i))
    (hden : ∀ i, ENNReal.ofReal (lam * d ^ 2) ≤ volume (Z i))
    (hlam : d ^ θ ≤ lam) (a t : ℕ → ℝ) (S : ℕ → Finset (Fin 3 → ℤ))
    (ha : ∀ j, j < J → 0 < a j ∧ 2 * a j ≤ (T.layer j).radius / 64)
    (hsize : ∀ j, j < J → d ^ θ * (T.layer j).radius ^ 2 ≤ lam * (a j) ^ 2 / 16)
    (hnest : ∀ j, j + 1 < J → ∃ k : ℕ, 0 < k ∧ a j = (k : ℝ) * a (j + 1))
    (hgrid : ∀ j, j < J → ∀ i, Z i ⊆ gridUnion (a j) (S j))
    (ht : ∀ j, j < J → 0 < t j)
    (hclass : ∀ j, j < J → ∀ z ∈ S j,
      t j * (a j) ^ 3 ≤ volume.real (E ∩ gridCell (a j) z) ∧
      ρ * volume.real (E ∩ gridCell (a j) z) ≤ t j * (a j) ^ 3) :
    Nonempty (HierarchyAnalysis T E d θ ρ) := by
  classical
  let W := hierarchyShading T Z a S
  have hWT (j) (hj : j ≤ J) (k : Fin (T.layer j).card) :=
    hierarchyShading_containment H hd hgap hZT ha S hj k
  have hmass (j) (hj : j ≤ J) (k : Fin (T.layer j).card) :
      ENNReal.ofReal (d ^ θ * (T.layer j).radius ^ 2) ≤ volume (W j k) := by
    by_cases hj' : j < J
    · dsimp only [W]
      rw [hierarchyShading, if_pos hj']
      exact descendant_shadow_density hd hZT hden hj (ha j hj').1 (S j)
        (hgrid j hj') (hsize j hj') k
    · have hjJ : j = J := by omega
      subst j
      dsimp only [W]
      rw [hierarchyShading_terminal, H.bottom_radius]
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hlam (sq_nonneg d))).trans (hden k)
  refine ⟨⟨W, terminalDensity J t, ?_, ?_, ?_, hWT, hmass, ?_, ?_⟩⟩
  · intro j hj
    unfold terminalDensity
    split_ifs with hj'
    · exact ht j hj'
    · exact zero_lt_one
  · simp [terminalDensity]
  · intro j hj k
    exact hierarchyShading_measurable T hZm a S j k
  · let k : Fin (T.layer 0).card := ⟨0, (T.layer 0).card_pos⟩
    have hm := hmass 0 (Nat.zero_le J) k
    rw [H.root_radius, one_pow, mul_one] at hm
    have hl := gridHull_local_density (ha 0 H.length_pos).1 (ht 0 H.length_pos).le (S 0) hE
      (fun z hz => (hclass 0 H.length_pos z hz).1) (descendantUnion T Z 0 k)
    have hv : ENNReal.ofReal (t 0) * volume (W 0 k) ≤ volume E := by
      simpa only [W, hierarchyShading, if_pos H.length_pos] using
        hl.trans (measure_mono inter_subset_left)
    rw [terminalDensity, if_pos H.length_pos, ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _)]
    calc
      _ = ENNReal.ofReal (t 0) * ENNReal.ofReal (d ^ θ) := mul_comm _ _
      _ ≤ ENNReal.ofReal (t 0) * volume (W 0 k) := mul_le_mul' le_rfl hm
      _ ≤ _ := hv
  · intro j hj k m e hep
    let U : Set Space := ⋃ i, W (j + 1) (e i)
    have hUT : U ⊆ Tube (T.layer j).radius ((T.layer j).position k) ((T.layer j).direction k) := by
      apply iUnion_subset
      intro i
      exact (hWT (j + 1) (by omega) (e i)).trans
        (by simpa only [hep i] using H.containment j hj (e i))
    have hUg : U ⊆ gridUnion (a j) (S j) := by
      apply iUnion_subset
      intro i
      dsimp only [W]
      by_cases hj' : j + 1 < J
      · rw [hierarchyShading, if_pos hj']
        obtain ⟨b, hb, he⟩ := hnest j hj'
        rw [he]
        apply gridHull_subset_coarse_grid (ha (j + 1) hj').1 hb
        rw [← he]
        exact descendantUnion_subset T (hgrid j hj) (j + 1) (e i)
      · rw [hierarchyShading, if_neg hj']
        exact descendantUnion_subset T (hgrid j hj) (j + 1) (e i)
    have hl : ENNReal.ofReal (terminalDensity J t (j + 1)) * volume U ≤ volume (E ∩ U) :=
      hierarchyShading_local_density T hE hZE a t S (fun hj' => (ha (j + 1) hj').1)
        (fun hj' => (ht (j + 1) hj').le)
        (fun hj' z hz => (hclass (j + 1) hj' z hz).1) m e
    have hh := grid_class_upper (ha j hj).1 hρ (S j) hE inter_subset_left
      (inter_subset_right.trans hUT) (inter_subset_right.trans hUg)
      (fun z hz => (hclass j hj z hz).2)
    have hcap := gridHull_tube_volume (ha j hj).1
      ((ha j hj).2.trans (by have := (H.positive j hj.le).le; linarith))
      (H.radius_bounds hj.le).2 (S j) ((T.layer j).position k) ((T.layer j).direction k) ((T.layer j).unit k)
    change ENNReal.ofReal (ρ * terminalDensity J t (j + 1)) * volume U ≤ _
    have htj : terminalDensity J t j = t j := if_pos hj
    rw [htj]
    calc
      _ = ENNReal.ofReal ρ * (ENNReal.ofReal (terminalDensity J t (j + 1)) * volume U) := by
        rw [ENNReal.ofReal_mul hρ, mul_assoc]
      _ ≤ ENNReal.ofReal ρ * volume (E ∩ U) := mul_le_mul' le_rfl hl
      _ ≤ ENNReal.ofReal (t j) * volume (gridHull (a j) (S j)
          (Tube (T.layer j).radius ((T.layer j).position k) ((T.layer j).direction k))) := hh
      _ ≤ ENNReal.ofReal (t j) * ENNReal.ofReal (256 * (T.layer j).radius ^ 2) := mul_le_mul' le_rfl hcap
      _ = _ := by rw [← ENNReal.ofReal_mul (ht j hj).le]; congr 1; ring

end WangZahlLot.Obl.wz_multiscale_finite_tower
