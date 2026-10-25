-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativePaletteTransfer, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativePaletteTransfer.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativePaletteTransfer.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativePaletteTransfer.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativePaletteTransfer.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NormalizedPosteriors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.CoarsePaletteTransfer

/-! Actual packet histories and affine-normalized velocity bins satisfy the
coarse-posterior palette change with no fixed delta0 loss in the ambiguity count. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped BigOperators

noncomputable def labelledVelocityPalette {W : ℕ} (a : ℝ)
    (z : Fin W × ((ℕ × (Fin 6 → ℝ)) × ℝ)) : ℤ × ℤ := velocityPalette a (v z.2.1)

noncomputable def PathData.labelledNormalizedPalette {W : ℕ} (p : PathData W)
    (b : Fin p.C) (a : ℝ) (z : Fin W × ((ℕ × (Fin 6 → ℝ)) × ℝ)) : ℤ × ℤ :=
  velocityPalette a (p.normalizedVelocity b z.2)

theorem measurable_euclidean_velocityPalette {Ω : Type*} [MeasurableSpace Ω]
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (hV : Measurable V) (a : ℝ) :
    Measurable (fun z => velocityPalette a (V z)) := by
  apply measurable_velocityPalette a
  apply Measurable.of_eval
  intro j
  exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) j).measurable.comp hV

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

def PreparedAngularPath.coarseSupport (i c : ℕ) :
    Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)) :=
  labelledSupport Q.residual ∩ {z | finitePacketHistory p.lev p.γ p.F i z = c}

noncomputable def PreparedAngularPath.coarseLaw (i c : ℕ) :
    Measure (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)) :=
  ProbabilityTheory.cond Q.law (Q.coarseSupport i c)

def PreparedAngularPath.normalizedPaletteCut (b : Fin p.C) (start stop c : ℕ)
    (a₀ a₁ R ε : ℝ) : Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)) :=
  coarsePaletteCut Q.law (labelledSupport Q.residual) (finitePacketHistory p.lev p.γ p.F)
    (labelledVelocityPalette a₀) (p.labelledNormalizedPalette b a₁) start stop c R ε

/-- The finite code theorem is instantiated on the ACTUAL original prepared
coarse law and the ACTUAL parent-normalized palette. -/
theorem PreparedAngularPath.normalized_palette_transfer (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (b : Fin p.C) (start stop c : ℕ) (hst : start ≤ stop)
    (hCpos : Q.law (Q.coarseSupport start c) ≠ 0)
    {a₀ a₁ ε R : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hε : 0 < ε) (hR : 0 ≤ R)
    (hmesh : a₀ * d.N k ^ (2 * δ₀ * d.L) ≤ a₁) (K : ℕ) (hK : (4 * p.κ + 6) ^ 2 ≤ (K : ℝ)) :
    MeasurableSet (Q.normalizedPaletteCut b start stop c a₀ a₁ R ε) ∧
      Q.normalizedPaletteCut b start stop c a₀ a₁ R ε ⊆
        likelihoodGood Q.law (labelledSupport Q.residual) (finitePacketHistory p.lev p.γ p.F)
          (labelledVelocityPalette a₀) start stop R ∩ Q.coarseSupport start c ∧
      (Q.coarseLaw start c).real
        ((likelihoodGood Q.law (labelledSupport Q.residual) (finitePacketHistory p.lev p.γ p.F)
          (labelledVelocityPalette a₀) start stop R ∩ Q.coarseSupport start c) \
          Q.normalizedPaletteCut b start stop c a₀ a₁ R ε) ≤ ε * (K : ℝ) ∧
      ∀ e a, (Q.coarseLaw start c).real
        {z | z ∈ Q.normalizedPaletteCut b start stop c a₀ a₁ R ε ∧
          finitePacketHistory p.lev p.γ p.F stop z = e ∧ p.labelledNormalizedPalette b a₁ z = a} ≤
          (R / ε) * (Q.coarseLaw start c).real {z | finitePacketHistory p.lev p.γ p.F stop z = e} *
            (Q.coarseLaw start c).real {z | p.labelledNormalizedPalette b a₁ z = a} := by
  classical
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  let := Q.probability hd hHE hκ
  let C := Q.coarseSupport start c
  let V : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 2) := fun z => v z.2.1
  let Z := labelledVelocityPalette (W := d.W k) a₀
  let Y := p.labelledNormalizedPalette b a₁
  have hF (a : Fin p.C) : MeasurableSet (p.F a) :=
    (hp.2.2.2.2.2.2.2 a).2.2.2.2.2.2.2.2.2.1
  have hV : Measurable V :=
    Submission.Obl.k4_dk4_smoothed_problem.Framework.continuous_planarVelocity.measurable.comp
      (measurable_fst.comp measurable_snd)
  have hZ : Measurable Z := measurable_euclidean_velocityPalette V hV a₀
  have hY : Measurable Y := measurable_euclidean_velocityPalette _
    ((p.measurable_normalizedVelocity b).comp measurable_snd) a₁
  have hSne : C.Nonempty := nonempty_of_measure_ne_zero hCpos
  have hVC : ∀ z ∈ C, ∀ j, |V z j| ≤ d.K k := by
    intro z hz j
    exact Q.velocity_bound z.1 z.2 (Q.residual_subset z.1 hz.1) j
  have hK0 : 0 ≤ d.K k := le_trans (by norm_num) (hd.2.2.1.1 k)
  obtain ⟨_, _, hZfin, _, _⟩ := velocityPalette_card C hSne (fun z j => V z j) hK0 ha₀ hVC
  have hN : 1 ≤ d.N k := le_trans (by norm_num) (hd.1 k)
  let q : ℝ := ((2 : ℝ) ^ p.T (p.lev b))⁻¹
  have hq : 0 ≤ q := by positivity
  have hmesh' : (q * ∑ i, ∑ j, |(p.Q b)⁻¹ i j|) * a₀ ≤ p.κ * a₁ := by
    calc
      _ ≤ (p.κ * d.N k ^ (2 * δ₀ * d.L)) * a₀ :=
        mul_le_mul_of_nonneg_right (hp.normalized_inverse_bound hN b) ha₀.le
      _ = p.κ * (a₀ * d.N k ^ (2 * δ₀ * d.L)) := by ring
      _ ≤ p.κ * a₁ := mul_le_mul_of_nonneg_left hmesh hκ.le
  have hEach (a : ℤ × ℤ) : (Y '' {z | z ∈ C ∧ Z z = a}).Finite ∧
      ((Y '' {z | z ∈ C ∧ Z z = a}).ncard : ℝ) ≤ (4 * p.κ + 6) ^ 2 := by
    by_cases hne : {z | z ∈ C ∧ Z z = a}.Nonempty
    · have hb : ∀ x ∈ {z | z ∈ C ∧ Z z = a}, ∀ x' ∈ {z | z ∈ C ∧ Z z = a},
          velocityPalette a₀ (V x) = velocityPalette a₀ (V x') :=
        fun _ hx _ hx' => hx.2.trans hx'.2.symm
      exact affine_velocity_palette_card_mesh _ hne V (p.Q b)⁻¹ (p.u b) hq ha₀ ha₁ hκ.le hmesh' hb
    · have he := Set.not_nonempty_iff_eq_empty.mp hne
      refine ⟨by simpa only [he, image_empty] using (Set.finite_empty : (∅ : Set (ℤ × ℤ)).Finite), ?_⟩
      simpa only [he, image_empty, Set.ncard_empty, Nat.cast_zero] using sq_nonneg (4 * p.κ + 6)
  have hYfin : (Y '' C).Finite := by
    have hs : Y '' C ⊆ ⋃ a ∈ Z '' C, Y '' {z | z ∈ C ∧ Z z = a} := by
      rintro _ ⟨z, hz, rfl⟩
      exact mem_iUnion.mpr ⟨Z z, mem_iUnion.mpr ⟨⟨z, hz, rfl⟩, ⟨z, ⟨hz, rfl⟩, rfl⟩⟩⟩
    exact (hZfin.biUnion (fun a _ => (hEach a).1)).subset hs
  have hK' (a : ℤ × ℤ) : (Y '' {z | z ∈ C ∧ Z z = a}).ncard ≤ K := by
    exact_mod_cast (hEach a).2.trans hK
  exact likelihood_coarse_palette_transfer Q.law (labelledSupport Q.residual)
    (measurableSet_labelledSupport Q.residual Q.residual_measurable)
    (finitePacketHistory p.lev p.γ p.F) Z Y start stop c
    (measurable_finitePacketHistory p.lev p.γ p.F hF start)
    (measurable_finitePacketHistory p.lev p.γ p.F hF stop) hZ hY
    (fun _ _ _ _ he => finitePacketHistory_nested p.lev p.γ p.F hst he) hCpos
    ((finite_finitePacketHistory_range p.lev p.γ p.F stop).subset (image_subset_range _ _))
    hZfin hYfin hε hR K hK'

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
