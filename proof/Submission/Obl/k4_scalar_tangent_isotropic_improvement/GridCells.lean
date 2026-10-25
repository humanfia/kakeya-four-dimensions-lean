import Submission.Obl.k4_matching_endpoint_volume.GridPacking

/-! Converting gridded base-cell ceilings to volume after cell thickening. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

open Set MeasureTheory
open scoped BigOperators

/-- The base grid may have an origin, so affine normalization preserves its cells. -/
def baseGridTag (o : Fin 2 → ℝ) (ξ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℤ :=
  Submission.Obl.k4_matching_endpoint_volume.gridTag ξ (x - o)

def baseGridCell (o : Fin 2 → ℝ) (ξ : ℝ) (q : Fin 2 → ℤ) : Set (Fin 2 → ℝ) :=
  Set.univ.pi (fun i => Set.Ico (o i + ξ * (q i : ℝ)) (o i + ξ * ((q i : ℝ) + 1)))

theorem measurableSet_baseGridCell (o : Fin 2 → ℝ) (ξ : ℝ) (q : Fin 2 → ℤ) :
    MeasurableSet (baseGridCell o ξ q) := MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

theorem mem_baseGridCell_iff (o : Fin 2 → ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (q : Fin 2 → ℤ) (x : Fin 2 → ℝ) : x ∈ baseGridCell o ξ q ↔ baseGridTag o ξ x = q := by
  constructor
  · intro hx
    funext i
    have hi := Set.mem_univ_pi.mp hx i
    change ⌊(x i - o i) / ξ⌋ = q i
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (le_div_iff₀ hξ).mpr
      nlinarith [hi.1]
    · apply (div_lt_iff₀ hξ).mpr
      nlinarith [hi.2]
  · intro hx
    apply Set.mem_univ_pi.mpr
    intro i
    have hi := congrFun hx i
    change ⌊(x i - o i) / ξ⌋ = q i at hi
    rw [Int.floor_eq_iff] at hi
    have hl := (le_div_iff₀ hξ).mp hi.1
    have hu := (div_lt_iff₀ hξ).mp hi.2
    constructor <;> nlinarith

theorem baseGridCell_pairwiseDisjoint (o : Fin 2 → ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    Pairwise (fun q q' => Disjoint (baseGridCell o ξ q) (baseGridCell o ξ q')) := by
  intro q q' hne
  apply Set.disjoint_left.mpr
  intro x hx hx'
  apply hne
  exact ((mem_baseGridCell_iff o hξ q x).mp hx).symm.trans
    ((mem_baseGridCell_iff o hξ q' x).mp hx')

theorem volume_baseGridCell (o : Fin 2 → ℝ) {ξ : ℝ} (hξ : 0 ≤ ξ) (q : Fin 2 → ℤ) :
    volume (baseGridCell o ξ q) = ENNReal.ofReal (ξ ^ 2) := by
  rw [baseGridCell, volume_pi_pi]
  have hv (i : Fin 2) : volume (Set.Ico (o i + ξ * (q i : ℝ))
      (o i + ξ * ((q i : ℝ) + 1))) = ENNReal.ofReal ξ := by
    rw [Real.volume_Ico]
    congr 1
    ring
  simp only [hv, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow hξ 2).symm

theorem dist_le_of_same_baseGridCell (o : Fin 2 → ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    {q : Fin 2 → ℤ} {x y : Fin 2 → ℝ}
    (hx : x ∈ baseGridCell o ξ q) (hy : y ∈ baseGridCell o ξ q) : dist x y ≤ ξ := by
  have htag := ((mem_baseGridCell_iff o hξ q x).mp hx).trans
    ((mem_baseGridCell_iff o hξ q y).mp hy).symm
  have h := Submission.Obl.k4_matching_endpoint_volume.dist_le_mesh_of_gridTag_eq hξ htag
  rw [dist_eq_norm, show (x - o) - (y - o) = x - y by abel] at h
  simpa only [dist_eq_norm] using h

/-- Bounded coordinate sets occupy finitely many base grid cells. -/
theorem baseGridTag_image_finite (o : Fin 2 → ℝ) {ξ R : ℝ} (hξ : 0 < ξ)
    (E : Set (Fin 2 → ℝ)) (hbound : ∀ x ∈ E, ∀ i, |x i - o i| ≤ R) :
    (baseGridTag o ξ '' E).Finite := by
  classical
  let lo : ℤ := ⌊-R / ξ⌋
  let hi : ℤ := ⌊R / ξ⌋
  let Q : Finset (Fin 2 → ℤ) := Fintype.piFinset (fun _ => Finset.Icc lo hi)
  apply Q.finite_toSet.subset
  rintro q ⟨x, hx, rfl⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  have hb := abs_le.mp (hbound x hx i)
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hb.1 hξ.le),
    Int.floor_mono (div_le_div_of_nonneg_right hb.2 hξ.le)⟩

/-- Cellwise ceilings give a volume bound after thickening to the entire
finite set of occupied cells. No absolute continuity is assumed. -/
theorem measure_le_thickened_grid_volume {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z : Ω → Fin 2 → ℝ) (o : Fin 2 → ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (E : Set Ω) (Q : Finset (Fin 2 → ℤ)) (C : ℝ)
    (hcover : ∀ ω ∈ E, baseGridTag o ξ (z ω) ∈ Q)
    (hcap : ∀ q ∈ Q, μ {ω | baseGridTag o ξ (z ω) = q} ≤
      ENNReal.ofReal C * ENNReal.ofReal (ξ ^ 2)) :
    μ E ≤ ENNReal.ofReal C * volume (⋃ q ∈ Q, baseGridCell o ξ q) := by
  classical
  have hsub : E ⊆ ⋃ q ∈ Q, {ω | baseGridTag o ξ (z ω) = q} := by
    intro ω hω
    exact Set.mem_iUnion₂.mpr ⟨baseGridTag o ξ (z ω), hcover ω hω, rfl⟩
  have hdisj : (↑Q : Set (Fin 2 → ℤ)).PairwiseDisjoint (baseGridCell o ξ) := by
    intro q hq q' hq' hne
    exact baseGridCell_pairwiseDisjoint o hξ hne
  calc
    μ E ≤ ∑ q ∈ Q, μ {ω | baseGridTag o ξ (z ω) = q} :=
      (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ q ∈ Q, ENNReal.ofReal C * ENNReal.ofReal (ξ ^ 2) := Finset.sum_le_sum hcap
    _ = ENNReal.ofReal C * (∑ q ∈ Q, volume (baseGridCell o ξ q)) := by
      rw [Finset.mul_sum]
      simp_rw [volume_baseGridCell o hξ.le]
    _ = _ := by rw [measure_biUnion_finset hdisj (fun q hq => measurableSet_baseGridCell o ξ q)]

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
