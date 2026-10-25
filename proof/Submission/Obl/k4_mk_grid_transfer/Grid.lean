import Submission.Obl.k4_mk_grid_transfer.Density

/-
Adapted from this LOT tree, obligation o003, session x0004, commit cf36787,
Submission/Obl/k4_multilinear_kakeya/Grid.lean.
-/

namespace Submission.Obl.k4_mk_grid_transfer

open MeasureTheory Set
open scoped ENNReal

def latticePoint {n : ℕ} (z : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => (z j : ℝ))

def latticeCell {n : ℕ} (z : Fin n → ℤ) : Set (EuclideanSpace ℝ (Fin n)) :=
  WithLp.ofLp ⁻¹' Set.univ.pi (fun j => Set.Ico (z j : ℝ) ((z j : ℝ) + 1))

lemma measurableSet_latticeCell {n : ℕ} (z : Fin n → ℤ) :
    MeasurableSet (latticeCell z) :=
  (MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).preimage
    (PiLp.volume_preserving_ofLp (Fin n)).measurable

lemma volume_latticeCell {n : ℕ} (z : Fin n → ℤ) : volume (latticeCell z) = 1 := by
  rw [latticeCell, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).nullMeasurableSet]
  simp [volume_pi_pi, Real.volume_Ico]

lemma iUnion_latticeCell (n : ℕ) :
    (⋃ z : Fin n → ℤ, latticeCell z) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  apply Set.mem_iUnion.mpr
  refine ⟨fun j => ⌊x j⌋, ?_⟩
  simp only [latticeCell, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ico]
  exact fun j => ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

lemma dist_latticePoint_lt_two {n : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4)
    (z : Fin n → ℤ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ latticeCell z) :
    dist x (latticePoint z) < 2 := by
  have hpos : 0 < n := by omega
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
  have hx' (j : Fin n) : 0 ≤ x j - (z j : ℝ) ∧ x j - (z j : ℝ) < 1 := by
    have h := Set.mem_univ_pi.mp hx j
    constructor <;> linarith [h.1, h.2]
  have hs : (∑ j : Fin n, (x j - (z j : ℝ)) ^ 2) < ∑ _j : Fin n, (1 : ℝ) := by
    apply Finset.sum_lt_sum_of_nonempty hne
    intro j _
    have h := hx' j
    nlinarith
  have hd : dist x (latticePoint z) ^ 2 = ∑ j : Fin n, (x j - (z j : ℝ)) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    rfl
  have hn4' : (n : ℝ) ≤ 4 := by exact_mod_cast hn4
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hs
  nlinarith [show 0 ≤ dist x (latticePoint z) from dist_nonneg]

lemma lintegral_le_lattice_tsum {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (g : (Fin n → ℤ) → ℝ≥0∞)
    (h : ∀ z x, x ∈ latticeCell z → f x ≤ g z) :
    (∫⁻ x, f x) ≤ ∑' z, g z := by
  calc
    (∫⁻ x, f x) = ∫⁻ x in ⋃ z : Fin n → ℤ, latticeCell z, f x := by
      rw [iUnion_latticeCell, Measure.restrict_univ]
    _ ≤ ∑' z : Fin n → ℤ, ∫⁻ x in latticeCell z, f x := lintegral_iUnion_le _ _
    _ ≤ ∑' z, g z := by
      apply ENNReal.tsum_le_tsum
      intro z
      calc
        (∫⁻ x in latticeCell z, f x) ≤ ∫⁻ _x in latticeCell z, g z :=
          setLIntegral_mono' (measurableSet_latticeCell z) (h z)
        _ = g z := by simp [lintegral_const, volume_latticeCell]

lemma lattice_tsum_le_of_fin_sum_le {n : ℕ} (g : (Fin n → ℤ) → ℝ≥0∞) (C : ℝ≥0∞)
    (h : ∀ (m : ℕ) (z : Fin m → (Fin n → ℤ)), Function.Injective z →
      (∑ q : Fin m, g (z q)) ≤ C) : (∑' z, g z) ≤ C := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  let e : Fin s.card ≃ s := s.equivFin.symm
  let z : Fin s.card → (Fin n → ℤ) := fun q => (e q).val
  have hz : Function.Injective z := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  have hs := h s.card z hz
  have he : (∑ q : Fin s.card, g (z q)) = ∑ q : s, g q :=
    e.sum_comp (fun q : s => g q)
  rw [he] at hs
  simpa only [Finset.sum_coe_sort] using hs

theorem unit_integral_le_grid {n : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4) {C : ℝ}
    (hgrid : ∀ (m : ℕ) (z : Fin m → (Fin n → ℤ)), Function.Injective z →
      ∀ (N : Fin n → ℕ)
        (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
        (w : (i : Fin n) → Fin (N i) → ℝ),
      (∀ i k, ‖e i k‖ = 1) → (∀ i k, 0 ≤ w i k) →
      (∑ q : Fin m, tubeSum 3 a e w (latticePoint (z q)) ^
        ((1 : ℝ) / ((n : ℝ) - 1))) ≤
        C * ∏ i : Fin n, (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1)))
    (N : Fin n → ℕ)
    (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
    (w : (i : Fin n) → Fin (N i) → ℝ)
    (he : ∀ i k, ‖e i k‖ = 1) (hw : ∀ i k, 0 ≤ w i k) :
    (∫⁻ x, ENNReal.ofReal (tubeSum 1 a e w x ^ ((1 : ℝ) / ((n : ℝ) - 1)))) ≤
      ENNReal.ofReal (C * ∏ i : Fin n,
        (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1))) := by
  have hp : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1) := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg zero_le_one (by linarith)
  apply le_trans (lintegral_le_lattice_tsum _
    (fun z => ENNReal.ofReal (tubeSum 3 a e w (latticePoint z) ^
      ((1 : ℝ) / ((n : ℝ) - 1)))) ?_) ?_
  · intro z x hx
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow (tubeSum_nonneg _ _ _ _ hw x)
      (tubeSum_le_nearby a e w hw (dist_latticePoint_lt_two hn hn4 z hx)) hp
  · apply lattice_tsum_le_of_fin_sum_le
    intro m z hz
    rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => Real.rpow_nonneg
      (tubeSum_nonneg _ _ _ _ hw _) _)]
    exact ENNReal.ofReal_le_ofReal (hgrid m z hz N a e w he hw)

end Submission.Obl.k4_mk_grid_transfer
