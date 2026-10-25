-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripAtlas, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripAtlas.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripAtlas.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripAtlas.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripAtlas.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripAssignments
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripPhysical
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripPolynomials
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripLists
import Submission.Lib.K4XInterface.Outputs

/-! The finite chart family obtained by refining one old time/depth level. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped RealInnerProductSpace BigOperators

structure StripParent (W T : ℕ) where
  world : Fin W
  timeIndex : Fin (2 ^ T)
  center : StripSpace
  velocity : StripSpace
  frame : Matrix (Fin 2) (Fin 2) ℝ
  test : MvPolynomial (Fin 4) ℝ
  trajectories : Set (ℕ × (Fin 6 → ℝ))
  incidences : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)

def StripParent.start {W T : ℕ} (b : StripParent W T) : ℝ :=
  (((b.timeIndex : ℕ) : ℝ)) / (2 : ℝ) ^ T

def StripParent.Valid {W T : ℕ} (b : StripParent W T) (N : ℝ) (M D : ℕ) (κ r : ℝ)
    (B : Fin W → ℝ) (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) : Prop :=
  gchart N M D κ T (((b.timeIndex : ℕ) : ℝ)) r (B b.world) (E b.world)
    b.center b.velocity b.frame b.test b.trajectories b.incidences True

structure StripRefinement (α : Type) where
  count : ℕ
  bins : ℕ
  normalBudget : ℕ
  radius : ℝ
  normal : α → Fin count → StripSpace
  tangent : α → Fin count → StripSpace
  offset : α → Fin count → ℝ

abbrev StripRefinement.Label {α : Type} (d : StripRefinement α) :=
  α × Fin d.count × {z : ℤ // z ∈ stripBinRange d.bins}

namespace StripRefinement

variable {α : Type} {W T : ℕ} (d : StripRefinement α) (p : α → StripParent W T)

def assignment (a : d.Label) : Set (ℕ × (Fin 6 → ℝ)) :=
  stripAssignment (p a.1).trajectories
    (packetVelocity (((2 : ℝ) ^ T)⁻¹) (p a.1).frame (p a.1).velocity)
    (fun l => packetPosition (p a.1).frame (p a.1).center (p a.1).velocity l
      ((p a.1).start + ((2 : ℝ) ^ T)⁻¹ / 2))
    (d.normal a.1) (d.offset a.1) ((d.normalBudget : ℝ) * d.radius) d.radius a.2.1 a.2.2

def incidence (a : d.Label) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  (p a.1).incidences ∩ Prod.fst ⁻¹' d.assignment p a

def center (a : d.Label) : StripSpace :=
  physicalStripCenter (p a.1).frame (p a.1).center (d.normal a.1 a.2.1)
    (p a.1).start (((2 : ℝ) ^ T)⁻¹) ((a.2.2 : ℤ) * d.radius) (d.offset a.1 a.2.1)

def velocity (a : d.Label) : StripSpace :=
  physicalStripVelocity (p a.1).frame (p a.1).velocity (d.normal a.1 a.2.1)
    (((2 : ℝ) ^ T)⁻¹) (d.offset a.1 a.2.1)

def frame (κ : ℝ) (a : d.Label) : Matrix (Fin 2) (Fin 2) ℝ :=
  (p a.1).frame * stripLocalFrame κ (d.normalBudget : ℝ) d.radius
    (d.tangent a.1 a.2.1) (d.normal a.1 a.2.1)

def refinedParent (κ : ℝ) (a : d.Label) : StripParent W T where
  world := (p a.1).world
  timeIndex := (p a.1).timeIndex
  center := d.center p a
  velocity := d.velocity p a
  frame := d.frame p κ a
  test := (p a.1).test
  trajectories := d.assignment p a
  incidences := d.incidence p a

theorem label_card [Fintype α] : Fintype.card d.Label = Fintype.card α *
    (d.count * (2 * d.bins + 1)) := by
  simp only [Label, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, stripBinRange_card]

theorem assignment_subset (a : d.Label) : d.assignment p a ⊆ (p a.1).trajectories := by
  intro l hl
  exact hl.1.1

theorem incidence_subset (a : d.Label) : d.incidence p a ⊆ (p a.1).incidences :=
  inter_subset_left

theorem incidence_assignment (a : d.Label) {x : (ℕ × (Fin 6 → ℝ)) × ℝ}
    (hx : x ∈ d.incidence p a) : x.1 ∈ d.assignment p a := hx.2

theorem measurableSet_assignment (hA : ∀ b, MeasurableSet (p b).trajectories)
    (a : d.Label) : MeasurableSet (d.assignment p a) := by
  apply measurableSet_stripAssignment _ _ _ _ _ _ _ _ _ (hA a.1)
  · exact (continuous_packetVelocity _ _ _).measurable
  · exact (continuous_packetPosition _ _ _ _).measurable

theorem measurableSet_incidence (hA : ∀ b, MeasurableSet (p b).trajectories)
    (hF : ∀ b, MeasurableSet (p b).incidences) (a : d.Label) :
    MeasurableSet (d.incidence p a) :=
  (hF a.1).inter ((d.measurableSet_assignment p hA a).preimage measurable_fst)

theorem assignment_disjoint
    (hold : ∀ b b', b ≠ b' → (p b).world = (p b').world →
      (p b).timeIndex = (p b').timeIndex → Disjoint (p b).trajectories (p b').trajectories)
    {a a' : d.Label} (hne : a ≠ a') (hw : (p a.1).world = (p a'.1).world)
    (ht : (p a.1).timeIndex = (p a'.1).timeIndex) :
    Disjoint (d.assignment p a) (d.assignment p a') := by
  rcases a with ⟨b, i, z⟩
  rcases a' with ⟨b', i', z'⟩
  by_cases hbb : b = b'
  · subst b'
    apply stripAssignment_disjoint
    intro h
    apply hne
    exact Prod.ext rfl (Prod.ext (congrArg (fun q : Fin d.count × ℤ => q.1) h)
      (Subtype.ext (congrArg (fun q : Fin d.count × ℤ => q.2) h)))
  · exact (hold b b' hbb hw ht).mono (d.assignment_subset p _) (d.assignment_subset p _)

theorem whole_block_fit {N κ depth : ℝ} {M D : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (hκ : 1 ≤ κ) (hr : 0 < d.radius)
    (he : ∀ b i, ‖d.tangent b i‖ = 1) (hn : ∀ b i, ‖d.normal b i‖ = 1)
    (hen : ∀ b i, inner ℝ (d.tangent b i) (d.normal b i) = 0)
    (a : d.Label) {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ d.assignment p a)
    {t : ℝ} (ht : t ∈ Set.Icc
      (((((p a.1).timeIndex : ℕ) : ℝ)) / (2 : ℝ) ^ T)
      (((((p a.1).timeIndex : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)) :
    ‖Matrix.toEuclideanLin (d.frame p κ a)⁻¹
      (gy l t - d.center p a - t • d.velocity p a)‖ ≤ 2 := by
  rcases hold a.1 with ⟨hQ, _, _, _, _, _, _, _, _, hgeo, _, _⟩
  have hq : 0 < ((2 : ℝ) ^ T)⁻¹ := by positivity
  have hend : (p a.1).start + ((2 : ℝ) ^ T)⁻¹ =
      (((((p a.1).timeIndex : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) := by
    unfold StripParent.start
    ring
  have hfit : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖packetPosition (p a.1).frame (p a.1).center (p a.1).velocity l
        ((p a.1).start + ((2 : ℝ) ^ T)⁻¹ * θ)‖ ≤ κ := by
    intro θ hθ
    apply ((hgeo l (d.assignment_subset p a hl)).2.2 _ _).1
    change _ ∈ Set.Icc (p a.1).start _
    rw [← hend]
    constructor <;> nlinarith [mul_nonneg hq.le hθ.1,
      mul_le_mul_of_nonneg_left hθ.2 hq.le]
  have hmid : |inner ℝ (packetPosition (p a.1).frame (p a.1).center
      (p a.1).velocity l ((p a.1).start + ((2 : ℝ) ^ T)⁻¹ / 2))
        (d.normal a.1 a.2.1) - (a.2.2 : ℤ) * d.radius| ≤ d.radius := by
    have h := midpoint_floor_center_bound hr
      (inner ℝ (packetPosition (p a.1).frame (p a.1).center (p a.1).velocity l
        ((p a.1).start + ((2 : ℝ) ^ T)⁻¹ / 2)) (d.normal a.1 a.2.1))
    rw [hl.2] at h
    exact h
  have ht' : t ∈ Set.Icc (p a.1).start ((p a.1).start + ((2 : ℝ) ^ T)⁻¹) := by
    constructor
    · simpa only [StripParent.start] using ht.1
    · rw [hend]
      exact ht.2
  exact physical_strip_whole_block_fit (p a.1).frame (p a.1).center (p a.1).velocity
    (d.tangent a.1 a.2.1) (d.normal a.1 a.2.1) l hQ hq (by linarith) (by positivity) hr
    (he _ _) (hn _ _) (hen _ _) hfit hl.1.2.1 hmid ht'

theorem assignment_format {N κ depth : ℝ} {M D : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (a : d.Label) (copy : ℕ) :
    gfmt 6 (N ^ M + 2 * (d.count : ℝ) + 2) (max D 1)
      {z | (copy, z) ∈ d.assignment p a} := by
  rcases hold a.1 with ⟨_, _, _, _, _, _, _, _, hfmt, _, _, _⟩
  exact packetStripAssignment_format {z | (copy, z) ∈ (p a.1).trajectories} copy
    (p a.1).frame (p a.1).center (p a.1).velocity (p a.1).start (((2 : ℝ) ^ T)⁻¹)
    (d.normal a.1) (d.offset a.1) a.2.1 a.2.2 (hfmt copy).1

theorem incidence_format {N κ depth : ℝ} {M D : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (a : d.Label) (copy : ℕ) :
    gfmt 7 (2 * N ^ M + 2 * (d.count : ℝ) + 2) (max D 1)
      {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈ d.incidence p a} := by
  rcases hold a.1 with ⟨_, _, _, _, _, _, _, _, hfmt, _, _, _⟩
  have hlift := Submission.Obl.k4_coarsened_outer_horizon_composition.fmt_polynomial_preimage
    (d.assignment_format p hold a copy)
    (fun j : Fin 6 => (MvPolynomial.X j.castSucc : MvPolynomial (Fin 7) ℝ))
    (d := 1) (fun _ => by simp)
  have h := gfmt_inter (hfmt copy).2 hlift
  convert h using 1
  · ring
  · simp
  · ext z
    simp only [incidence, mem_ofPred_eq, mem_inter_iff, mem_preimage, MvPolynomial.eval_X]

/-- Reframing retains the old test and produces genuine charts once the explicit
polynomial budgets and actual slack have been checked. -/
theorem valid {N κ κ' depth : ℝ} {M M' D : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (hN : 1 ≤ N) (hM : M ≤ M')
    (hκ : 1 ≤ κ) (hκκ : κ ≤ κ') (hκ' : 4 ≤ κ') (hB : ∀ w, 0 ≤ B w)
    (hr : 0 < d.radius)
    (he : ∀ b i, ‖d.tangent b i‖ = 1) (hn : ∀ b i, ‖d.normal b i‖ = 1)
    (hen : ∀ b i, inner ℝ (d.tangent b i) (d.normal b i) = 0)
    (hformat : 2 * N ^ M + 2 * (d.count : ℝ) + 2 ≤ N ^ M')
    (hdata : ∀ a : d.Label,
      ‖d.center p a‖ + ‖d.velocity p a‖ ≤ N ^ M' ∧
      (∑ i : Fin 2, ∑ j : Fin 2, (|d.frame p κ a i j| + |(d.frame p κ a)⁻¹ i j|)) ≤ N ^ M' ∧
      (∑ i : Fin 2, ∑ j : Fin 2, |d.frame p κ a i j|) ≤ κ' / (2 : ℝ) ^ T)
    (a : d.Label) :
    (d.refinedParent p κ a).Valid N M' (max D 1) κ' depth B E := by
  have hdet : (d.frame p κ a).det ≠ 0 := by
    rw [frame, Matrix.det_mul]
    apply mul_ne_zero (hold a.1).1
    apply abs_pos.mp
    rw [stripLocalFrame_abs_det (by linarith) (by positivity) hr (he _ _) (hn _ _) (hen _ _)]
    positivity
  let f := (d.frame p κ a)⁻¹
  have hf : f.det ≠ 0 := by
    dsimp [f]
    rw [det_inv_fin2]
    exact inv_ne_zero hdet
  have hfinv : f⁻¹ = d.frame p κ a := inv_inv_of_det_ne_zero _ hdet
  have hA (b : α) : MeasurableSet (p b).trajectories := by
    rcases hold b with ⟨_, _, _, _, _, _, h, _⟩
    exact h
  have hF (b : α) : MeasurableSet (p b).incidences := by
    rcases hold b with ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  have hAcount : N ^ M + 2 * (d.count : ℝ) + 2 ≤ N ^ M' := by
    have hpow : 0 ≤ N ^ M := by positivity
    linarith
  have h := gchart_reframe (hold a.1) hN hM (le_max_left D 1) (by linarith) hκκ
    (hB _) f hf (d.center p a) (d.velocity p a) (a := 2) (b := 2) (by linarith)
    (A' := d.assignment p a) (F' := d.incidence p a) (ex' := True)
    (fun l hl t ht => by
      have hfit := d.whole_block_fit p hold hκ hr he hn hen a hl ht
      constructor
      · have hc := (PiLp.norm_apply_le
          (Matrix.toEuclideanLin f (gy l t - d.center p a - t • d.velocity p a)) 0).trans hfit
        simpa only [Real.norm_eq_abs, toEuclideanLin_apply_fin2] using hc
      · have hc := (PiLp.norm_apply_le
          (Matrix.toEuclideanLin f (gy l t - d.center p a - t • d.velocity p a)) 1).trans hfit
        simpa only [Real.norm_eq_abs, toEuclideanLin_apply_fin2] using hc)
    (hdata a).1 (by rw [hfinv]; exact (hdata a).2.1)
    (by rw [hfinv]; exact (hdata a).2.2)
    (d.assignment_subset p a) (d.incidence_subset p a)
    (fun _ hx => d.incidence_assignment p a hx)
    (d.measurableSet_assignment p hA a) (d.measurableSet_incidence p hA hF a)
    (fun copy => ⟨gfmt_mono hAcount le_rfl (d.assignment_format p hold a copy),
      gfmt_mono hformat le_rfl (d.incidence_format p hold a copy)⟩) True.intro
  rw [hfinv] at h
  exact h

end StripRefinement

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
