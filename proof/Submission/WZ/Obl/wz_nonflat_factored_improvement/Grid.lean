-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.Grid.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseGeometry

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

noncomputable section

def gridCell (b : ℝ) (z : Fin 3 → ℤ) : Set Space :=
  {p | ∀ i, (z i : ℝ) * b ≤ p i ∧ p i < ((z i : ℝ) + 1) * b}

def gridKey (b : ℝ) (p : Space) : Fin 3 → ℤ := fun i => ⌊p i / b⌋

theorem mem_gridCell_iff {b : ℝ} (hb : 0 < b) (z : Fin 3 → ℤ) (p : Space) :
    p ∈ gridCell b z ↔ gridKey b p = z := by
  constructor
  · intro hp
    funext i
    exact Int.floor_eq_iff.mpr ⟨(le_div_iff₀ hb).mpr (hp i).1, (div_lt_iff₀ hb).mpr (hp i).2⟩
  · intro hp i
    have hi := congrFun hp i
    change ⌊p i / b⌋ = z i at hi
    have hh := Int.floor_eq_iff.mp hi
    exact ⟨(le_div_iff₀ hb).mp hh.1, (div_lt_iff₀ hb).mp hh.2⟩

theorem mem_gridCell_key {b : ℝ} (hb : 0 < b) (p : Space) : p ∈ gridCell b (gridKey b p) :=
  (mem_gridCell_iff hb _ _).mpr rfl

theorem gridCell_disjoint {b : ℝ} (hb : 0 < b) :
    Pairwise (fun z z' : Fin 3 → ℤ => Disjoint (gridCell b z) (gridCell b z')) := by
  intro z z' hne
  apply Set.disjoint_left.mpr
  intro p hp hp'
  exact hne (((mem_gridCell_iff hb z p).mp hp).symm.trans ((mem_gridCell_iff hb z' p).mp hp'))

theorem gridCell_eq_preimage (b : ℝ) (z : Fin 3 → ℤ) :
    gridCell b z = WithLp.ofLp ⁻¹'
      (Set.pi Set.univ (fun i => Set.Ico ((z i : ℝ) * b) (((z i : ℝ) + 1) * b))) := by
  ext p
  simp [gridCell, Set.mem_pi]

theorem gridCell_measurable (b : ℝ) (z : Fin 3 → ℤ) : MeasurableSet (gridCell b z) := by
  rw [gridCell_eq_preimage]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Ico).preimage
    (PiLp.volume_preserving_ofLp (Fin 3)).measurable

theorem gridCell_volume {b : ℝ} (hb : 0 ≤ b) (z : Fin 3 → ℤ) :
    volume (gridCell b z) = ENNReal.ofReal (b ^ 3) := by
  rw [gridCell_eq_preimage, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    ((MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet), volume_pi_pi]
  simp only [Real.volume_Ico]
  have he (i : Fin 3) : ((z i : ℝ) + 1) * b - (z i : ℝ) * b = b := by ring
  simp only [he, Fin.prod_univ_three]
  rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul (mul_nonneg hb hb)]
  congr 1
  ring

theorem gridCell_dist_lt {b : ℝ} (hb : 0 < b) {z : Fin 3 → ℤ} {p q : Space}
    (hp : p ∈ gridCell b z) (hq : q ∈ gridCell b z) : dist p q < 2 * b := by
  have hcoord (i : Fin 3) : |p i - q i| ≤ b := by
    rw [abs_le]
    constructor <;> linarith [(hp i).1, (hp i).2, (hq i).1, (hq i).2]
  have hsq : ‖p - q‖ ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 + (p 2 - q 2) ^ 2 := by
    simpa using WangZahlLot.Obl.wz_affine_robust_cluster_estimate.norm_sq_coords (p - q)
  have h0 := sq_le_sq' (abs_le.mp (hcoord 0)).1 (abs_le.mp (hcoord 0)).2
  have h1 := sq_le_sq' (abs_le.mp (hcoord 1)).1 (abs_le.mp (hcoord 1)).2
  have h2 := sq_le_sq' (abs_le.mp (hcoord 2)).1 (abs_le.mp (hcoord 2)).2
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (p - q), sq_pos_of_pos hb]

theorem gridCell_subset_neighborhood {b : ℝ} (hb : 0 < b) {z : Fin 3 → ℤ} {S : Set Space}
    (h : (S ∩ gridCell b z).Nonempty) : gridCell b z ⊆ thickening (2 * b) S := by
  obtain ⟨p, hp, hpz⟩ := h
  intro q hq
  exact mem_thickening_iff.mpr ⟨p, hp, gridCell_dist_lt hb hq hpz⟩

def gridKeys (b : ℝ) : Finset (Fin 3 → ℤ) :=
  Finset.Icc (fun _ => -(⌈2 / b⌉₊ : ℤ)) (fun _ => (⌈2 / b⌉₊ : ℤ))

theorem gridKey_mem {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {p : Space} (hp : p ∈ unitBall) :
    gridKey b p ∈ gridKeys b := by
  have hp' : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hb' : 1 ≤ 1 / b := (one_le_div hb).mpr hb1
  have hK : 2 / b ≤ (⌈2 / b⌉₊ : ℝ) := Nat.le_ceil _
  have hc (i : Fin 3) : -(⌈2 / b⌉₊ : ℤ) ≤ gridKey b p i ∧
      gridKey b p i ≤ (⌈2 / b⌉₊ : ℤ) := by
    have hpi : |p i| < 1 := by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le p i).trans_lt hp'
    have hl : -(1 / b) < p i / b := by
      rw [← neg_div]
      exact (div_lt_div_iff_of_pos_right hb).mpr (abs_lt.mp hpi).1
    have hu : p i / b < 1 / b := (div_lt_div_iff_of_pos_right hb).mpr (abs_lt.mp hpi).2
    have hf := Int.floor_le (p i / b)
    have hf' := Int.lt_floor_add_one (p i / b)
    have htwo : 2 / b = 2 * (1 / b) := by ring
    nth_rw 1 [htwo] at hK
    have hlow : -(⌈2 / b⌉₊ : ℝ) ≤ (⌊p i / b⌋ : ℤ) := by linarith
    have hupp : (⌊p i / b⌋ : ℤ) ≤ (⌈2 / b⌉₊ : ℝ) := by linarith
    constructor
    · exact_mod_cast hlow
    · exact_mod_cast hupp
  exact Finset.mem_Icc.mpr ⟨fun i => (hc i).1, fun i => (hc i).2⟩

theorem grid_covers_unitBall {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    unitBall ⊆ ⋃ z ∈ gridKeys b, gridCell b z := by
  intro p hp
  exact Set.mem_iUnion.mpr ⟨gridKey b p, Set.mem_iUnion.mpr
    ⟨gridKey_mem hb hb1 hp, mem_gridCell_key hb p⟩⟩

end

end WangZahlLot.Obl.wz_nonflat_factored_improvement
