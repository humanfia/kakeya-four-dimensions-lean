-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripMergedAtlas, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripMergedAtlas.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripMergedAtlas.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripMergedAtlas.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripMergedAtlas.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMergedFormat
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripAtlas

/-! The second-scale merged chart family. Its geometric frame is the already
checked strip frame of the canonical representative; only its trajectory and
incidence predicates change. The success event can be a finite union of old
fine-packet events, without encoding any analytic deletion mask. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped RealInnerProductSpace BigOperators

namespace StripRefinement

variable {α : Type} {W T : ℕ} (d : StripRefinement α) (p : α → StripParent W T)

abbrev MergedLabel := Σ b : α,
  StripCodeLabel d.radius (d.normal b) (d.offset b) ×
    {z : ℤ // z ∈ stripBinRange d.bins}

def mergedCanonicalLabel (a : d.MergedLabel) : d.Label :=
  (a.1, canonicalStripIndex d.radius (d.normal a.1) (d.offset a.1) a.2.1, a.2.2)

def mergedAssignment (w : ℝ) (a : d.MergedLabel) : Set (ℕ × (Fin 6 → ℝ)) :=
  mergedStripAssignment (p a.1).trajectories
    (packetVelocity (((2 : ℝ) ^ T)⁻¹) (p a.1).frame (p a.1).velocity)
    (fun l => packetPosition (p a.1).frame (p a.1).center (p a.1).velocity l
      ((p a.1).start + ((2 : ℝ) ^ T)⁻¹ / 2))
    d.radius (d.normal a.1) (d.offset a.1) w a.2.1 a.2.2

def mergedIncidence (w : ℝ)
    (success : α → StripParameterCode → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (a : d.MergedLabel) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  ((p a.1).incidences ∩ Prod.fst ⁻¹' d.mergedAssignment p w a) ∩
    success a.1 a.2.1.val

def mergedParent (κ w : ℝ)
    (success : α → StripParameterCode → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (a : d.MergedLabel) : StripParent W T where
  world := (p a.1).world
  timeIndex := (p a.1).timeIndex
  center := d.center p (d.mergedCanonicalLabel a)
  velocity := d.velocity p (d.mergedCanonicalLabel a)
  frame := d.frame p κ (d.mergedCanonicalLabel a)
  test := (p a.1).test
  trajectories := d.mergedAssignment p w a
  incidences := d.mergedIncidence p w success a

theorem mergedLabel_card_le [Fintype α] :
    Fintype.card d.MergedLabel ≤ Fintype.card α * (d.count * (2 * d.bins + 1)) := by
  classical
  simp only [MergedLabel, Fintype.card_sigma, Fintype.card_prod, Fintype.card_coe,
    stripBinRange_card]
  calc
    _ ≤ ∑ _b : α, d.count * (2 * d.bins + 1) := by
      apply Finset.sum_le_sum
      intro b _
      apply Nat.mul_le_mul_right
      simpa only [StripCodeLabel, Fintype.card_coe] using
        stripCodeLabel_card_le d.radius (d.normal b) (d.offset b)
    _ = _ := by simp

theorem mergedAssignment_subset (w : ℝ) (a : d.MergedLabel) :
    d.mergedAssignment p w a ⊆ (p a.1).trajectories := by
  intro l hl
  exact hl.1.1

theorem mergedIncidence_subset (w : ℝ)
    (success : α → StripParameterCode → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (a : d.MergedLabel) : d.mergedIncidence p w success a ⊆ (p a.1).incidences :=
  fun _ hx => hx.1.1

theorem measurableSet_mergedAssignment (w : ℝ)
    (hA : ∀ b, MeasurableSet (p b).trajectories) (a : d.MergedLabel) :
    MeasurableSet (d.mergedAssignment p w a) := by
  apply measurableSet_mergedStripAssignment _ _ _ _ _ _ _ _ _ (hA a.1)
  · exact (continuous_packetVelocity _ _ _).measurable
  · exact (continuous_packetPosition _ _ _ _).measurable

theorem measurableSet_mergedIncidence (w : ℝ)
    (success : α → StripParameterCode → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hA : ∀ b, MeasurableSet (p b).trajectories)
    (hF : ∀ b, MeasurableSet (p b).incidences)
    (hS : ∀ b q, MeasurableSet (success b q)) (a : d.MergedLabel) :
    MeasurableSet (d.mergedIncidence p w success a) :=
  ((hF a.1).inter ((d.measurableSet_mergedAssignment p w hA a).preimage measurable_fst)).inter
    (hS _ _)

theorem mergedAssignment_disjoint (w : ℝ)
    (hold : ∀ b b', b ≠ b' → (p b).world = (p b').world →
      (p b).timeIndex = (p b').timeIndex → Disjoint (p b).trajectories (p b').trajectories)
    {a a' : d.MergedLabel} (hne : a ≠ a') (hw : (p a.1).world = (p a'.1).world)
    (ht : (p a.1).timeIndex = (p a'.1).timeIndex) :
    Disjoint (d.mergedAssignment p w a) (d.mergedAssignment p w a') := by
  rcases a with ⟨b, q, z⟩
  rcases a' with ⟨b', q', z'⟩
  by_cases hbb : b = b'
  · subst b'
    apply mergedStripAssignment_disjoint
    intro h
    apply hne
    apply congrArg (fun v => (Sigma.mk b v : d.MergedLabel))
    exact Prod.ext (congrArg (fun q : StripCodeLabel d.radius (d.normal b) (d.offset b) × ℤ => q.1) h)
      (Subtype.ext (congrArg (fun q : StripCodeLabel d.radius (d.normal b) (d.offset b) × ℤ => q.2) h))
  · exact (hold b b' hbb hw ht).mono (d.mergedAssignment_subset p _ _)
      (d.mergedAssignment_subset p _ _)

theorem mergedAssignment_format {N κ depth : ℝ} {M D : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (w : ℝ)
    (a : d.MergedLabel) (copy : ℕ) :
    gfmt 6 (N ^ M + 2 * (d.count : ℝ) + 2) (max D 1)
      {z | (copy, z) ∈ d.mergedAssignment p w a} := by
  rcases hold a.1 with ⟨_, _, _, _, _, _, _, _, hfmt, _, _, _⟩
  exact packetMergedStripAssignment_format {z | (copy, z) ∈ (p a.1).trajectories} copy
    (p a.1).frame (p a.1).center (p a.1).velocity (p a.1).start (((2 : ℝ) ^ T)⁻¹)
    (d.normal a.1) (d.offset a.1) a.2.1 a.2.2 (hfmt copy).1

theorem mergedIncidence_format {N κ depth Hs : ℝ} {M D Ds : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (w : ℝ)
    (success : α → StripParameterCode → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hS : ∀ b q copy, gfmt 7 Hs Ds
      {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈ success b q})
    (a : d.MergedLabel) (copy : ℕ) :
    gfmt 7 (2 * N ^ M + 2 * (d.count : ℝ) + 2 + Hs) (max (max D 1) Ds)
      {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈
        d.mergedIncidence p w success a} := by
  rcases hold a.1 with ⟨_, _, _, _, _, _, _, _, hfmt, _, _, _⟩
  have hlift := Submission.Obl.k4_coarsened_outer_horizon_composition.fmt_polynomial_preimage
    (d.mergedAssignment_format p hold w a copy)
    (fun j : Fin 6 => (MvPolynomial.X j.castSucc : MvPolynomial (Fin 7) ℝ))
    (d := 1) (fun _ => by simp)
  have h := gfmt_inter (gfmt_inter (hfmt copy).2 hlift) (hS a.1 a.2.1.val copy)
  convert h using 1
  · ring
  · simp
  · ext z
    simp only [mergedIncidence, mem_ofPred_eq, mem_inter_iff, mem_preimage,
      MvPolynomial.eval_X]

theorem merged_whole_block_fit {N κ depth w : ℝ} {M D : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (hκ : 1 ≤ κ) (hr : 0 < d.radius)
    (he : ∀ b i, ‖d.tangent b i‖ = 1) (hn : ∀ b i, ‖d.normal b i‖ = 1)
    (hen : ∀ b i, inner ℝ (d.tangent b i) (d.normal b i) = 0)
    (hV : ∀ b l, l ∈ (p b).trajectories →
      ‖packetVelocity (((2 : ℝ) ^ T)⁻¹) (p b).frame (p b).velocity l‖ ≤ 2 * κ)
    (hwidth : w + 3 * (1 + 2 * κ) * d.radius ≤ (d.normalBudget : ℝ) * d.radius)
    (a : d.MergedLabel) {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ d.mergedAssignment p w a)
    {t : ℝ} (ht : t ∈ Set.Icc
      (((((p a.1).timeIndex : ℕ) : ℝ)) / (2 : ℝ) ^ T)
      (((((p a.1).timeIndex : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)) :
    ‖Matrix.toEuclideanLin (d.frame p κ (d.mergedCanonicalLabel a))⁻¹
      (gy l t - d.center p (d.mergedCanonicalLabel a) -
        t • d.velocity p (d.mergedCanonicalLabel a))‖ ≤ 2 := by
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
    apply ((hgeo l (d.mergedAssignment_subset p w a hl)).2.2 _ _).1
    change _ ∈ Set.Icc (p a.1).start _
    rw [← hend]
    constructor <;> nlinarith [mul_nonneg hq.le hθ.1,
      mul_le_mul_of_nonneg_left hθ.2 hq.le]
  have hmid : |inner ℝ (packetPosition (p a.1).frame (p a.1).center
      (p a.1).velocity l ((p a.1).start + ((2 : ℝ) ^ T)⁻¹ / 2))
        (d.normal a.1 (d.mergedCanonicalLabel a).2.1) - (a.2.2 : ℤ) * d.radius| ≤
      d.radius := by
    have h := midpoint_floor_center_bound hr
      (inner ℝ (packetPosition (p a.1).frame (p a.1).center (p a.1).velocity l
        ((p a.1).start + ((2 : ℝ) ^ T)⁻¹ / 2))
          (d.normal a.1 (d.mergedCanonicalLabel a).2.1))
    dsimp only [mergedCanonicalLabel] at h
    rw [hl.2] at h
    exact h
  have ht' : t ∈ Set.Icc (p a.1).start ((p a.1).start + ((2 : ℝ) ^ T)⁻¹) := by
    constructor
    · simpa only [StripParent.start] using ht.1
    · rw [hend]
      exact ht.2
  exact physical_strip_whole_block_fit (p a.1).frame (p a.1).center (p a.1).velocity
    (d.tangent a.1 (d.mergedCanonicalLabel a).2.1)
    (d.normal a.1 (d.mergedCanonicalLabel a).2.1) l hQ hq (by linarith) (by positivity) hr
    (he _ _) (hn _ _) (hen _ _) hfit
    ((mergedStripCell_velocity_bound hr (by linarith) (hV _ _ hl.1.1) hl.1.2).trans hwidth)
    hmid ht'

theorem merged_valid {N κ κ' depth w Hs : ℝ} {M M' D Ds : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (hN : 1 ≤ N) (hM : M ≤ M')
    (hκ : 1 ≤ κ) (hκκ : κ ≤ κ') (hκ' : 4 ≤ κ') (hB : ∀ w, 0 ≤ B w)
    (hr : 0 < d.radius)
    (he : ∀ b i, ‖d.tangent b i‖ = 1) (hn : ∀ b i, ‖d.normal b i‖ = 1)
    (hen : ∀ b i, inner ℝ (d.tangent b i) (d.normal b i) = 0)
    (hV : ∀ b l, l ∈ (p b).trajectories →
      ‖packetVelocity (((2 : ℝ) ^ T)⁻¹) (p b).frame (p b).velocity l‖ ≤ 2 * κ)
    (hwidth : w + 3 * (1 + 2 * κ) * d.radius ≤ (d.normalBudget : ℝ) * d.radius)
    (success : α → StripParameterCode → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hSmeas : ∀ b q, MeasurableSet (success b q)) (hHs : 0 ≤ Hs)
    (hS : ∀ b q copy, gfmt 7 Hs Ds
      {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈ success b q})
    (hformat : 2 * N ^ M + 2 * (d.count : ℝ) + 2 + Hs ≤ N ^ M')
    (hdata : ∀ a : d.Label,
      ‖d.center p a‖ + ‖d.velocity p a‖ ≤ N ^ M' ∧
      (∑ i : Fin 2, ∑ j : Fin 2, (|d.frame p κ a i j| + |(d.frame p κ a)⁻¹ i j|)) ≤ N ^ M' ∧
      (∑ i : Fin 2, ∑ j : Fin 2, |d.frame p κ a i j|) ≤ κ' / (2 : ℝ) ^ T)
    (a : d.MergedLabel) :
    (d.mergedParent p κ w success a).Valid N M' (max (max D 1) Ds) κ' depth B E := by
  let v := d.mergedCanonicalLabel a
  have hdet : (d.frame p κ v).det ≠ 0 := by
    rw [frame, Matrix.det_mul]
    apply mul_ne_zero (hold a.1).1
    apply abs_pos.mp
    rw [stripLocalFrame_abs_det (by linarith) (by positivity) hr (he _ _) (hn _ _) (hen _ _)]
    positivity
  let f := (d.frame p κ v)⁻¹
  have hf : f.det ≠ 0 := by
    dsimp [f]
    rw [det_inv_fin2]
    exact inv_ne_zero hdet
  have hfinv : f⁻¹ = d.frame p κ v := inv_inv_of_det_ne_zero _ hdet
  have hA (b : α) : MeasurableSet (p b).trajectories := by
    rcases hold b with ⟨_, _, _, _, _, _, h, _⟩
    exact h
  have hF (b : α) : MeasurableSet (p b).incidences := by
    rcases hold b with ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  have hAcount : N ^ M + 2 * (d.count : ℝ) + 2 ≤ N ^ M' := by
    have hpow : 0 ≤ N ^ M := by positivity
    linarith
  have h := gchart_reframe (hold a.1) hN hM
    ((le_max_left D 1).trans (le_max_left (max D 1) Ds)) (by linarith) hκκ
    (hB _) f hf (d.center p v) (d.velocity p v) (a := 2) (b := 2) (by linarith)
    (A' := d.mergedAssignment p w a) (F' := d.mergedIncidence p w success a) (ex' := True)
    (fun l hl t ht => by
      have hfit := d.merged_whole_block_fit p hold hκ hr he hn hen hV hwidth a hl ht
      constructor
      · have hc := (PiLp.norm_apply_le
          (Matrix.toEuclideanLin f (gy l t - d.center p v - t • d.velocity p v)) 0).trans hfit
        simpa only [Real.norm_eq_abs, toEuclideanLin_apply_fin2] using hc
      · have hc := (PiLp.norm_apply_le
          (Matrix.toEuclideanLin f (gy l t - d.center p v - t • d.velocity p v)) 1).trans hfit
        simpa only [Real.norm_eq_abs, toEuclideanLin_apply_fin2] using hc)
    (hdata v).1 (by rw [hfinv]; exact (hdata v).2.1)
    (by rw [hfinv]; exact (hdata v).2.2)
    (d.mergedAssignment_subset p w a) (d.mergedIncidence_subset p w success a)
    (fun _ hx => hx.1.2)
    (d.measurableSet_mergedAssignment p w hA a)
    (d.measurableSet_mergedIncidence p w success hA hF hSmeas a)
    (fun copy => ⟨gfmt_mono hAcount (le_max_left _ _) (d.mergedAssignment_format p hold w a copy),
      gfmt_mono hformat le_rfl (d.mergedIncidence_format p hold w success hS a copy)⟩)
    True.intro
  rw [hfinv] at h
  exact h

end StripRefinement

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
