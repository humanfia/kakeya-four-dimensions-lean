-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SimultaneousChildStates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalDescendantReferences
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Clauses
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.SameLevelPacketCuts

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath)
open scoped ENNReal BigOperators

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- Assemble actual child-state producers BEFORE whole-ancestor-code
choices. The same global surviving source has exactly each child's own
state law; its total deletion pays only one original-reference budget.
The local input is supplied by `OriginalAncestorRecordSource.relative_states_with_graph_code`.
All child state and palette functions remain available after assembly. -/
theorem assemble_simultaneous_child_states
    {Code : Type*}
    (selected : Set (Fin p.C)) (level : ℕ) (hlevel : ∀ b∈selected, p.lev b=level)
    (E : Fin (d.W k) → Set Ev) (hE : ∀ w, MeasurableSet (E w))
    (hbase : ∀ w, E w⊆Q.base w)
    (K : ℝ) (eps pv : Fin p.C → ℝ)
    (base : Fin p.C → Ev → O204.Split.P3) (signal : Fin p.C → Ev → ℝ)
    (graph : Fin p.C → Ev → Code) (row : Fin p.C → Code → Fin 3 → ℝ)
    (bound : Fin p.C → ℝ) (charge : ENNReal)
    (hlocal : ∀ b, b∈selected →
      ∃ (keep : Set Ev) (state : Ev → ℕ) (value : ℕ → Fin 3 → ℝ)
        (palette : Measure (Fin 2 → ℤ)),
        keep⊆E (p.γ b)∩p.F b ∧
        ((d.ν k (p.γ b)).prod volume) (E (p.γ b)∩p.F b) ≤
          ((d.ν k (p.γ b)).prod volume) keep+
            charge*(d.ν k (p.γ b) (p.A b)*
              ENNReal.ofReal (((2:ℝ)^p.T (p.lev b))⁻¹)) ∧
        StateClauses K (eps b) (pv b) (d.ν k (p.γ b)) (base b) (signal b)
          keep state palette ∧
        (∀ z, value (state z)=row b (graph b z)) ∧
        (∀ j c, |value j c| ≤ bound b) ∧
        ∀ x y, state x=state y → graph b x=graph b y) :
    ∃ (keep : Fin (d.W k) → Set Ev)
      (localKeep : (b : Fin p.C) → b∈selected → Set Ev)
      (state : (b : Fin p.C) → b∈selected → Ev → ℕ)
      (value : (b : Fin p.C) → b∈selected → ℕ → Fin 3 → ℝ)
      (palette : (b : Fin p.C) → b∈selected → Measure (Fin 2 → ℤ)),
      (∀ w, MeasurableSet (keep w) ∧ keep w⊆E w) ∧
      (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (E w\keep w)) ≤ charge ∧
      ∀ b (hb : b∈selected),
        keep (p.γ b)∩p.F b=localKeep b hb ∧
        StateClauses K (eps b) (pv b) (d.ν k (p.γ b)) (base b) (signal b)
          (keep (p.γ b)∩p.F b) (state b hb) (palette b hb) ∧
        (∀ z, value b hb (state b hb z)=row b (graph b z)) ∧
        (∀ j c, |value b hb j c| ≤ bound b) ∧
        ∀ x y, state b hb x=state b hb y → graph b x=graph b y := by
  classical
  choose localKeep state value palette hsub hmass hstates hvalue hbound hfaith using hlocal
  let G := fun b => if hb : b∈selected then localKeep b hb else univ
  have hG (b) (hb : b∈selected) : MeasurableSet (G b) := by
    simpa only [G,dif_pos hb] using (hstates b hb).1
  have hcut (b) (hb : b∈selected) :
      ((d.ν k (p.γ b)).prod volume) ((E (p.γ b)∩p.F b)\G b) ≤
        charge*(d.ν k (p.γ b) (p.A b)*
          ENNReal.ofReal (((2:ℝ)^p.T (p.lev b))⁻¹)) := by
    letI : IsProbabilityMeasure (d.ν k (p.γ b)) := (hd.weights k).2.2 _
    have hsubFull : localKeep b hb⊆p.fullCylinder b :=
      fun z hz => hp.counted_subset_fullCylinder b (hsub b hb hz).2
    have hfiniteRef : d.ν k (p.γ b) (p.A b)*
        ENNReal.ofReal (((2:ℝ)^p.T (p.lev b))⁻¹)≠⊤ :=
      ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
    have hfinite : ((d.ν k (p.γ b)).prod volume) (localKeep b hb)≠⊤ := by
      apply ne_top_of_le_ne_top hfiniteRef
      exact (measure_mono hsubFull).trans_eq (p.fullCylinder_mass (d.ν k (p.γ b)) b)
    simp only [G,dif_pos hb]
    exact (measure_sdiff_le_iff_le_add (hstates b hb).1.nullMeasurableSet
      (hsub b hb) hfinite).mpr (hmass b hb)
  obtain ⟨keep,hkeep,hloss,hslices⟩ := Q.assemble_same_level_packet_cuts hd hp
    selected level hlevel E hE hbase G hG charge hcut
  refine ⟨keep,localKeep,state,value,palette,hkeep,hloss,?_⟩
  intro b hb
  have hs : keep (p.γ b)∩p.F b=localKeep b hb := by
    rw [hslices b hb]
    simpa only [G,dif_pos hb] using inter_eq_right.mpr (hsub b hb)
  refine ⟨hs,?_,hvalue b hb,hbound b hb,hfaith b hb⟩
  rw [hs]
  exact hstates b hb

/-- Preserve arbitrary EXTRA actual bounds on the same local laws
while assembling child-state producers BEFORE whole-ancestor-code
choices. The same global surviving source has exactly each child's own
state law; its total deletion pays only one original-reference budget.
The local input is supplied by `OriginalAncestorRecordSource.relative_states_with_graph_code`.
All child state and palette functions remain available after assembly. -/
theorem assemble_simultaneous_child_states_with_extra
    {Code : Type*}
    (selected : Set (Fin p.C)) (level : ℕ) (hlevel : ∀ b∈selected, p.lev b=level)
    (E : Fin (d.W k) → Set Ev) (hE : ∀ w, MeasurableSet (E w))
    (hbase : ∀ w, E w⊆Q.base w)
    (K : ℝ) (eps pv : Fin p.C → ℝ)
    (base : Fin p.C → Ev → O204.Split.P3) (signal : Fin p.C → Ev → ℝ)
    (graph : Fin p.C → Ev → Code) (row : Fin p.C → Code → Fin 3 → ℝ)
    (bound : Fin p.C → ℝ) (charge : ENNReal)
    (Extra : Fin p.C → Set Ev → (Ev → ℕ) → (ℕ → Fin 3 → ℝ) → Measure (Fin 2 → ℤ) → Prop)
    (hlocal : ∀ b, b∈selected →
      ∃ (keep : Set Ev) (state : Ev → ℕ) (value : ℕ → Fin 3 → ℝ)
        (palette : Measure (Fin 2 → ℤ)),
        keep⊆E (p.γ b)∩p.F b ∧
        ((d.ν k (p.γ b)).prod volume) (E (p.γ b)∩p.F b) ≤
          ((d.ν k (p.γ b)).prod volume) keep+
            charge*(d.ν k (p.γ b) (p.A b)*
              ENNReal.ofReal (((2:ℝ)^p.T (p.lev b))⁻¹)) ∧
        StateClauses K (eps b) (pv b) (d.ν k (p.γ b)) (base b) (signal b)
          keep state palette ∧
        (∀ z, value (state z)=row b (graph b z)) ∧
        (∀ j c, |value j c| ≤ bound b) ∧
        (∀ x y, state x=state y → graph b x=graph b y) ∧
        Extra b keep state value palette) :
    ∃ (keep : Fin (d.W k) → Set Ev)
      (localKeep : (b : Fin p.C) → b∈selected → Set Ev)
      (state : (b : Fin p.C) → b∈selected → Ev → ℕ)
      (value : (b : Fin p.C) → b∈selected → ℕ → Fin 3 → ℝ)
      (palette : (b : Fin p.C) → b∈selected → Measure (Fin 2 → ℤ)),
      (∀ w, MeasurableSet (keep w) ∧ keep w⊆E w) ∧
      (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (E w\keep w)) ≤ charge ∧
      ∀ b (hb : b∈selected),
        keep (p.γ b)∩p.F b=localKeep b hb ∧
        StateClauses K (eps b) (pv b) (d.ν k (p.γ b)) (base b) (signal b)
          (keep (p.γ b)∩p.F b) (state b hb) (palette b hb) ∧
        (∀ z, value b hb (state b hb z)=row b (graph b z)) ∧
        (∀ j c, |value b hb j c| ≤ bound b) ∧
        (∀ x y, state b hb x=state b hb y → graph b x=graph b y) ∧
        Extra b (keep (p.γ b)∩p.F b) (state b hb) (value b hb) (palette b hb) := by
  classical
  choose localKeep state value palette hsub hmass hstates hvalue hbound hfaith hextra using hlocal
  let G := fun b => if hb : b∈selected then localKeep b hb else univ
  have hG (b) (hb : b∈selected) : MeasurableSet (G b) := by
    simpa only [G,dif_pos hb] using (hstates b hb).1
  have hcut (b) (hb : b∈selected) :
      ((d.ν k (p.γ b)).prod volume) ((E (p.γ b)∩p.F b)\G b) ≤
        charge*(d.ν k (p.γ b) (p.A b)*
          ENNReal.ofReal (((2:ℝ)^p.T (p.lev b))⁻¹)) := by
    letI : IsProbabilityMeasure (d.ν k (p.γ b)) := (hd.weights k).2.2 _
    have hsubFull : localKeep b hb⊆p.fullCylinder b :=
      fun z hz => hp.counted_subset_fullCylinder b (hsub b hb hz).2
    have hfiniteRef : d.ν k (p.γ b) (p.A b)*
        ENNReal.ofReal (((2:ℝ)^p.T (p.lev b))⁻¹)≠⊤ :=
      ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
    have hfinite : ((d.ν k (p.γ b)).prod volume) (localKeep b hb)≠⊤ := by
      apply ne_top_of_le_ne_top hfiniteRef
      exact (measure_mono hsubFull).trans_eq (p.fullCylinder_mass (d.ν k (p.γ b)) b)
    simp only [G,dif_pos hb]
    exact (measure_sdiff_le_iff_le_add (hstates b hb).1.nullMeasurableSet
      (hsub b hb) hfinite).mpr (hmass b hb)
  obtain ⟨keep,hkeep,hloss,hslices⟩ := Q.assemble_same_level_packet_cuts hd hp
    selected level hlevel E hE hbase G hG charge hcut
  refine ⟨keep,localKeep,state,value,palette,hkeep,hloss,?_⟩
  intro b hb
  have hs : keep (p.γ b)∩p.F b=localKeep b hb := by
    rw [hslices b hb]
    simpa only [G,dif_pos hb] using inter_eq_right.mpr (hsub b hb)
  refine ⟨hs,?_,hvalue b hb,hbound b hb,hfaith b hb,?_⟩
  · rw [hs]
    exact hstates b hb
  · rw [hs]
    exact hextra b hb

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
