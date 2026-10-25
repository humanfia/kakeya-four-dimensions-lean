-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourcePrep
import Submission.Obl.k4_finite_affine_parent_sources.IncidenceFloors

/-!
# Local floor pruning inside a parent packet

Packets of distinct labels of one level and world are almost disjoint, and the packets of
the descendants of a parent at one level fit in the parent packet. Hence pruning any set of
the parent packet to give every met descendant (and the parent) a floor `τ` of its packet
costs at most `#levels · τ` times the parent packet (`IncidenceFloors`).

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open Submission.Obl.k4_finite_forest_width_selection

noncomputable section

/-- Two closed dyadic blocks of one level with different indices meet in a null set. -/
theorem dyadic_blocks_inter_null (T j j' : ℕ) (hne : j ≠ j') :
    volume (Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T) ∩
      Icc ((j' : ℝ) / (2 : ℝ) ^ T) (((j' : ℝ) + 1) / (2 : ℝ) ^ T)) = 0 := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · -- the intersection lies in the single point `j' / 2^T`
    have hsub : Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T) ∩
        Icc ((j' : ℝ) / (2 : ℝ) ^ T) (((j' : ℝ) + 1) / (2 : ℝ) ^ T) ⊆
        Icc ((j' : ℝ) / (2 : ℝ) ^ T) ((j' : ℝ) / (2 : ℝ) ^ T) := by
      intro x hx
      refine ⟨hx.2.1, le_trans hx.1.2 ?_⟩
      apply div_le_div_of_nonneg_right _ h2.le
      have : ((j + 1 : ℕ) : ℝ) ≤ (j' : ℝ) := by exact_mod_cast h
      push_cast at this; exact this
    exact measure_mono_null hsub (by simp)
  · have hsub : Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T) ∩
        Icc ((j' : ℝ) / (2 : ℝ) ^ T) (((j' : ℝ) + 1) / (2 : ℝ) ^ T) ⊆
        Icc ((j : ℝ) / (2 : ℝ) ^ T) ((j : ℝ) / (2 : ℝ) ^ T) := by
      intro x hx
      refine ⟨hx.1.1, le_trans hx.2.2 ?_⟩
      apply div_le_div_of_nonneg_right _ h2.le
      have : ((j' + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
      push_cast at this; exact this
    exact measure_mono_null hsub (by simp)

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- Packets of distinct labels of one level and world are almost disjoint. -/
theorem packet_aedisjoint (w : Fin W) {b b' : Fin p.C} (hne : b ≠ b')
    (hlev : p.lev b = p.lev b') (hw : p.world b = w) (hw' : p.world b' = w) :
    AEDisjoint ((ν w).prod volume) (p.packet b) (p.packet b') := by
  unfold AEDisjoint PathData.packet
  rw [Set.prod_inter_prod, Measure.prod_prod]
  by_cases hbin : p.bin b = p.bin b'
  · have hd := hp.assignment_disjoint b b' hne hlev (hw.trans hw'.symm) hbin
    rw [Set.disjoint_iff_inter_eq_empty.mp hd, measure_empty, zero_mul]
  · rw [hlev, dyadic_blocks_inter_null _ _ _ hbin, mul_zero]

omit hp in
/-- Packets have finite measure under a finite world prior. -/
theorem packet_ne_top (w : Fin W) [IsFiniteMeasure (ν w)] (b : Fin p.C) :
    ((ν w).prod volume) (p.packet b) ≠ ⊤ := by
  unfold PathData.packet
  rw [Measure.prod_prod, Real.volume_Icc]
  exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top

theorem packet_measurable (b : Fin p.C) : MeasurableSet (p.packet b) :=
  (hp.assigned_measurable b).prod measurableSet_Icc

/-- The packet of a descendant lies in the packet of its ancestor. -/
theorem packet_subset_of_desc {a b : Fin p.C} (hab : p.lev a ≤ p.lev b)
    (hanc : forestAncestor p.lev p.par b (p.lev a) = a) : p.packet b ⊆ p.packet a := by
  have hA := hp.ancestor_assignment_subset b (p.lev a) hab
  have hT := hp.ancestor_time_subset b (p.lev a) hab
  rw [hanc] at hA hT
  exact Set.prod_mono hA hT

/-- The packets of the descendants of `a` at one level fill at most the packet of `a`. -/
theorem desc_packets_sum (a : Fin p.C) [IsFiniteMeasure (ν (p.world a))] (i : ℕ) :
    ∑ b ∈ Finset.univ.filter (fun b => p.lev b = i ∧ p.lev a ≤ p.lev b ∧
        forestAncestor p.lev p.par b (p.lev a) = a),
      (((ν (p.world a)).prod volume) (p.packet b)).toReal ≤
      (((ν (p.world a)).prod volume) (p.packet a)).toReal := by
  set s := Finset.univ.filter (fun b => p.lev b = i ∧ p.lev a ≤ p.lev b ∧
    forestAncestor p.lev p.par b (p.lev a) = a) with hs
  have hmem : ∀ b ∈ s, p.lev b = i ∧ p.lev a ≤ p.lev b ∧
      forestAncestor p.lev p.par b (p.lev a) = a := fun b hb => (Finset.mem_filter.mp hb).2
  have hworld : ∀ b ∈ s, p.world b = p.world a := by
    intro b hb
    have h := (hp.ancestor b (p.lev a) (hmem b hb).2.1).2.1
    rw [(hmem b hb).2.2] at h
    exact h.symm
  rw [← ENNReal.toReal_sum (fun b _ => packet_ne_top (p.world a) b)]
  apply ENNReal.toReal_mono (packet_ne_top _ a)
  rw [← measure_biUnion_finset₀]
  · apply measure_mono
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨b, hb, hzb⟩ := hz
    exact packet_subset_of_desc hp (hmem b hb).2.1 (hmem b hb).2.2 hzb
  · intro b hb b' hb' hne
    exact packet_aedisjoint hp (p.world a) hne ((hmem b hb).1.trans (hmem b' hb').1.symm)
      (hworld b hb) (hworld b' hb')
  · intro b _
    exact (packet_measurable hp b).nullMeasurableSet

/-- **Local floor pruning.** Inside the packet of `a`, prune a set so that every
descendant of `a` met by it keeps a floor `τ` of its packet; the loss is at most
`m τ` times the packet of `a`. -/
theorem exists_local_floors (a : Fin p.C) [IsFiniteMeasure (ν (p.world a))]
    {S₁ : Set Incidence} (hS₁ : MeasurableSet S₁) (hsub : S₁ ⊆ p.packet a)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ S ⊆ S₁, MeasurableSet S ∧
      (((ν (p.world a)).prod volume) S₁).toReal -
          m * τ * (((ν (p.world a)).prod volume) (p.packet a)).toReal ≤
        (((ν (p.world a)).prod volume) S).toReal ∧
      ∀ b : Fin p.C, p.lev a ≤ p.lev b → forestAncestor p.lev p.par b (p.lev a) = a →
        (S ∩ p.counted b).Nonempty →
        ENNReal.ofReal τ * ((ν (p.world a)).prod volume) (p.packet b) ≤
          ((ν (p.world a)).prod volume) (S ∩ p.counted b) := by
  set μ : Measure Incidence := (ν (p.world a)).prod (volume : Measure ℝ) with hμ
  have hfin : μ (p.packet a) ≠ ⊤ := packet_ne_top (p.world a) a
  have : IsFiniteMeasure (μ.restrict (p.packet a)) := isFiniteMeasure_restrict.mpr hfin
  let thr : Fin p.C → ℝ := fun b =>
    if p.lev a ≤ p.lev b ∧ forestAncestor p.lev p.par b (p.lev a) = a then
      τ * (μ (p.packet b)).toReal else 0
  have hthr : ∀ b, 0 ≤ thr b := by
    intro b
    simp only [thr]
    split_ifs
    · exact mul_nonneg hτ ENNReal.toReal_nonneg
    · exact le_rfl
  obtain ⟨E, hEm, hEU, hEmass, hEfl⟩ := exists_simultaneous_incidence_floors
    (μ.restrict (p.packet a)) S₁ hS₁ p.counted hp.counted_measurable thr hthr
  have hreal : ∀ X, MeasurableSet X → X ⊆ p.packet a →
      (μ.restrict (p.packet a)).real X = (μ X).toReal := by
    intro X hX hXa
    rw [Measure.real, Measure.restrict_apply hX, Set.inter_eq_left.mpr hXa]
  have hsum : ∑ b, thr b ≤ m * τ * (μ (p.packet a)).toReal := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := p.lev) (t := Finset.range m)
      (fun b _ => Finset.mem_range.mpr (hp.label_level b))]
    calc ∑ i ∈ Finset.range m, ∑ b ∈ Finset.univ.filter (fun b => p.lev b = i), thr b
        ≤ ∑ _i ∈ Finset.range m, τ * (μ (p.packet a)).toReal := by
          apply Finset.sum_le_sum
          intro i _
          have h : ∑ b ∈ Finset.univ.filter (fun b => p.lev b = i), thr b =
              ∑ b ∈ (Finset.univ.filter (fun b => p.lev b = i)).filter
                (fun b => p.lev a ≤ p.lev b ∧ forestAncestor p.lev p.par b (p.lev a) = a),
                τ * (μ (p.packet b)).toReal := (Finset.sum_filter _ _).symm
          rw [h, Finset.filter_filter, ← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (desc_packets_sum hp a i) hτ
      _ = m * τ * (μ (p.packet a)).toReal := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  refine ⟨E, hEU, hEm, ?_, ?_⟩
  · rw [← hreal S₁ hS₁ hsub, ← hreal E hEm (hEU.trans hsub)]
    linarith
  · intro b hab hanc hne
    have h := hEfl b hne
    have hthrb : thr b = τ * (μ (p.packet b)).toReal := ite_eq_left ⟨hab, hanc⟩
    rw [hthrb, Measure.real, Measure.restrict_apply (hEm.inter (hp.counted_measurable b))] at h
    have hfin' : μ (E ∩ p.counted b ∩ p.packet a) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_right)
    calc ENNReal.ofReal τ * μ (p.packet b)
        = ENNReal.ofReal (τ * (μ (p.packet b)).toReal) := by
          rw [ENNReal.ofReal_mul hτ, ENNReal.ofReal_toReal (packet_ne_top _ b)]
      _ ≤ ENNReal.ofReal ((μ (E ∩ p.counted b ∩ p.packet a)).toReal) :=
          ENNReal.ofReal_le_ofReal h
      _ = μ (E ∩ p.counted b ∩ p.packet a) := ENNReal.ofReal_toReal hfin'
      _ ≤ μ (E ∩ p.counted b) := measure_mono Set.inter_subset_left

end Path

namespace SourceData

variable {W : ℕ} {p : PathData W} (D : SourceData p)

/-- The open parent window lies in the parent packet. -/
theorem open_subset_packet :
    p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀) ⊆ p.packet D.parent := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  have h := Set.Ioo_subset_Icc_self hz.2
  rw [D.t₀_add_q₀] at h
  exact h

section Valid

variable {m Mp Dp : ℕ} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- Floors on every met descendant of the parent give the parent floor and the label
floors of the stage. -/
theorem floors_of_desc (hdepth : ∀ s, D.i₀ ≤ D.depth s) {τ : ℝ}
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (hterm : D.S ⊆ TerminalInc W p.C m p.lev p.world p.counted D.w₀)
    (hne : D.S.Nonempty)
    (hfl : ∀ b : Fin p.C, p.lev D.parent ≤ p.lev b →
      forestAncestor p.lev p.par b (p.lev D.parent) = D.parent →
      (D.S ∩ p.counted b).Nonempty →
      ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet b) ≤
        ((ν D.w₀).prod volume) (D.S ∩ p.counted b)) :
    (ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet D.parent) ≤
      ((ν D.w₀).prod volume) (D.S ∩ p.counted D.parent)) ∧
    (∀ s : ℝ, ∀ i : Fin (p.activeCount D.Hm (D.depth s)),
      ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet (D.old s i)) ≤
        ((ν D.w₀).prod volume) (D.S ∩ p.counted (D.old s i))) := by
  refine ⟨?_, ?_⟩
  · apply hfl D.parent le_rfl (forestAncestor_self _ _ _)
    obtain ⟨z, hz⟩ := hne
    exact ⟨z, hz, D.S_counted hp hSo hterm hz⟩
  · intro s i
    have hlev : p.lev D.parent ≤ p.lev (D.old s i) := by
      rw [D.old_level s i]; exact hdepth s
    exact hfl (D.old s i) hlev (D.old_ancestor hp hSo s (hdepth s) i) (D.old_world s i).2

end Valid

end SourceData

end

end Submission.Obl.k4_finite_affine_parent_sources
