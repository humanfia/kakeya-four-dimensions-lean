-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.DerivativeListsFromDyadicFloors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalDyadicFloorData
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DerivativeListsFromIncidences
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PureCellCanonicalCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CoarseDerivativeLists

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- The actual derivative tables prepared before the final child states.
The full original coefficient table and each ordinary spatial key stay fixed. -/
structure OriginalDerivativeListData {Λ I : Type*} (c : Λ → Fin 7 → ℝ)
    (E : Set (Λ × ℝ)) (level : I → ℕ) (listBound : I → ℝ) where
  lists : I → (Fin 4 → ℤ) → (Fin 2 → ℤ) → Finset ℤ
  card : ∀ i q v, ((lists i q v).card:ℝ) ≤ listBound i
  known : ∀ i z, z∈E →
    ⌊(c z.1 1+2*c z.1 2*z.2)/dyadicParameterWidth (level i)⌋∈
      lists i (originalFineState c (dyadicParameterWidth (level i)) z)
        (parameterCode (dyadicParameterWidth (level i)) (zv (c z.1)))

/-- Arbitrary later source cuts preserve the prepared derivative tables. -/
def OriginalDerivativeListData.restrict {Λ I : Type*} {c : Λ → Fin 7 → ℝ}
    {E : Set (Λ × ℝ)} {level : I → ℕ} {listBound : I → ℝ}
    (data : OriginalDerivativeListData c E level listBound)
    {S : Set (Λ × ℝ)} (hSE : S⊆E) : OriginalDerivativeListData c S level listBound :=
  ⟨data.lists,data.card,fun i z hz => data.known i z (hSE hz)⟩

/-- Consecutive original floors and resolved current pure numerators
construct the ordinary-cell derivative lists on any finite subgrid.
This is one actual source cut; no parameter palettes or lists are inputs. -/
theorem prepare_derivative_lists_of_dyadic_floors {Λ I : Type*}
    [MeasurableSpace Λ] [Fintype I]
    (μ : Measure (Λ × ℝ)) (ν : Measure Λ)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1)
    (H : ℕ) (hH : 1 ≤ (H:ℝ)) (hcoeff : ∀ z∈E, ∀ j, |c z.1 j| ≤ H)
    {palette : Measure (Fin 2 → ℝ)} {dimension exponent : ℝ} {start count : ℕ}
    (floors : OriginalDyadicFloorData ν c E palette dimension exponent start count)
    (hdim : 0 ≤ dimension)
    (level : I → ℕ) (hstart : ∀ i, start ≤ level i) (hstop : ∀ i, level i < start+count)
    (cut : I → ℝ) (hcut : ∀ i, 0 < cut i)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hδlevel : ∀ i, δ ≤ dyadicParameterWidth (level i))
    (hsmall : ∀ i, 3*((H:ℝ)+1)*δ ≤ dyadicParameterWidth (level i))
    (hpure : ∀ (i : I) (w : ℝ), δ ≤ w → w ≤ 1 → ∀ (b : Fin 3 → ℤ) (j : ℤ) (v : Fin 2 → ℤ),
      (μ.restrict E) {z | originalBaseCode c δ z=b ∧ ⌊zx (c z.1) z.2/w⌋=j ∧
        parameterCode (dyadicParameterWidth (level i)) (zv (c z.1))=v} ≤
          ENNReal.ofReal (C*δ^3*w^dimension)*
            (palette.map (parameterCode (dyadicParameterWidth (level i)))) {v}) :
    ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R⊆E ∧
      μ (E\R) ≤ (∑ i, ENNReal.ofReal (cut i*zoomBlockVisitConstant))*ν univ ∧
      Nonempty (OriginalDerivativeListData c R level (fun i =>
        (2*(H:ℝ)+3)^7*(6*(H:ℝ)+12)^4*
          ((151200*(12*(H:ℝ)+3)*C*(3:ℝ)^dimension)*
            (dyadicParameterWidth (level i))^(-exponent)/cut i)*
              (2*(⌈2*(H:ℝ)+5⌉:ℝ)+1))) := by
  let width : I → ℝ := fun i => dyadicParameterWidth (level i)
  let amp : I → ℝ := fun i => (width i)^dimension
  let K : I → ℝ := fun i => (width i)^(-exponent)
  let Ccanon : ℝ := 151200*(12*(H:ℝ)+3)*C*(3:ℝ)^dimension
  let weight : I → (Fin 2 → ℤ) → ENNReal := fun i v =>
    (palette.map (parameterCode (width i))) {v}
  have hwidth (i : I) : 0 < width i := dyadicParameterWidth_pos _
  have hw1 (i : I) : width i ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  letI : IsProbabilityMeasure palette := floors.probability
  have hweight (i : I) (v : Fin 2 → ℤ) : weight i v≠∞ := by
    letI : IsProbabilityMeasure (palette.map (parameterCode (width i))) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_parameterCode _).aemeasurable).mpr inferInstance
    exact measure_ne_top _ _
  have hfloor (i : I) (z : Λ × ℝ) (hz : z∈E) :
      ENNReal.ofReal ((width i)^2*amp i/K i)*
        weight i (parameterCode (width i) (zv (c z.1))) ≤
      ν {l | parameterCode (width i) (c l)=parameterCode (width i) (c z.1)} := by
    let j : Fin count := ⟨level i-start,by have := hstart i; have := hstop i; omega⟩
    have hj : start+j.val=level i := by have := hstart i; dsimp only [j]; omega
    have hh := floors.floor j z hz
    rw [hj] at hh
    have heq : (width i)^2*amp i/K i=(width i)^((2:ℝ)+dimension)*(width i)^exponent := by
      dsimp only [amp,K]
      rw [Real.rpow_neg (hwidth i).le,div_inv_eq_mul,Real.rpow_add (hwidth i),Real.rpow_two]
    have hvelocity (w : ℝ) (cf : Fin 7 → ℝ) : vbin w cf=parameterCode w (zv cf) := rfl
    simpa only [heq,width,weight,hvelocity] using hh
  have hcap (i : I) := canonical_cell_cap_of_current_pure_cells μ c hc E hE
    hδ (by norm_num : (0:ℝ)<1) le_rfl (hwidth i) (hw1 i)
    (hδlevel i) (by simpa only [one_mul,width] using hδlevel i) hH hC hdim
    (by simpa only [one_mul,width] using hsmall i) ht hcoeff (weight i) (hweight i)
    (by simpa only [one_mul,width,weight] using hpure i)
  have hcap' (i : I) (world cell v) :
      (μ.restrict E) {z | parameterCode 1 (c z.1)=world ∧
        canonicalZoomCell c 1 (width i) z=cell ∧ parameterCode (width i) (zv (c z.1))=v} ≤
      ENNReal.ofReal (Ccanon*width i*(width i)^2*amp i)*weight i v := by
    have hh := hcap i world cell v
    simpa only [one_mul,Ccanon,amp,Real.rpow_add (hwidth i),Real.rpow_two,mul_assoc] using hh
  obtain ⟨R,hR,hRE,hloss,lists,hcard,hknown⟩ :=
    prepare_derivative_lists_from_incidences μ ν c hc E hE ht H hcoeff level amp K (fun _ => Ccanon) cut
      (fun i => Real.rpow_pos_of_pos (hwidth i) _) (fun i => Real.rpow_pos_of_pos (hwidth i) _)
      (fun _ => by dsimp only [Ccanon]; positivity) hcut weight hweight hfloor hcap'
  exact ⟨R,hR,hRE,hloss,⟨fun i q v => lists i (q,v),fun i q v => hcard i (q,v),hknown⟩⟩

/-- Include the coarse prefix without demanding tiny-width coefficient
floors there. The scalar quadratic itself supplies that prefix. -/
theorem prepare_all_derivative_lists_of_dyadic_floors {Λ I : Type*}
    [MeasurableSpace Λ] [Fintype I]
    (μ : Measure (Λ × ℝ)) (ν : Measure Λ)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1)
    (H : ℕ) (hH : 1 ≤ (H:ℝ)) (hcoeff : ∀ z∈E, ∀ j, |c z.1 j| ≤ H)
    {palette : Measure (Fin 2 → ℝ)} {dimension exponent : ℝ} {start count : ℕ}
    (floors : OriginalDyadicFloorData ν c E palette dimension exponent start count)
    (hdim : 0 ≤ dimension)
    (level : I → ℕ) (hstop : ∀ i, level i < start+count)
    (cut : I → ℝ) (hcut : ∀ i, 0 < cut i)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hδlevel : ∀ i, δ ≤ dyadicParameterWidth (level i))
    (hsmall : ∀ i, 3*((H:ℝ)+1)*δ ≤ dyadicParameterWidth (level i))
    (hpure : ∀ (i : I) (w : ℝ), δ ≤ w → w ≤ 1 → ∀ (b : Fin 3 → ℤ) (j : ℤ) (v : Fin 2 → ℤ),
      (μ.restrict E) {z | originalBaseCode c δ z=b ∧ ⌊zx (c z.1) z.2/w⌋=j ∧
        parameterCode (dyadicParameterWidth (level i)) (zv (c z.1))=v} ≤
          ENNReal.ofReal (C*δ^3*w^dimension)*
            (palette.map (parameterCode (dyadicParameterWidth (level i)))) {v}) :
    ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R⊆E ∧
      μ (E\R) ≤ (∑ i : {i : I // start ≤ level i}, ENNReal.ofReal (cut i.val*zoomBlockVisitConstant))*ν univ ∧
      Nonempty (OriginalDerivativeListData c R level (fun i =>
        max (6*(H:ℝ)/dyadicParameterWidth start+2)
          ((2*(H:ℝ)+3)^7*(6*(H:ℝ)+12)^4*
            ((151200*(12*(H:ℝ)+3)*C*(3:ℝ)^dimension)*
              (dyadicParameterWidth (level i))^(-exponent)/cut i)*
                (2*(⌈2*(H:ℝ)+5⌉:ℝ)+1)))) := by
  classical
  obtain ⟨R,hR,hRE,hloss,⟨data⟩⟩ := prepare_derivative_lists_of_dyadic_floors μ ν c hc E hE ht H hH hcoeff
    floors hdim (fun i : {i : I // start ≤ level i} => level i.val) (fun i => i.property)
    (fun i => hstop i.val) (fun i => cut i.val) (fun i => hcut i.val) hδ hC
    (fun i => hδlevel i.val) (fun i => hsmall i.val) (fun i => hpure i.val)
  obtain ⟨coarse,hcoarse,hcoarseKnown⟩ := exists_coarse_derivative_lists R c
    (zero_le_one.trans hH) (dyadicParameterWidth_pos start)
    (fun i : {i : I // level i < start} => dyadicParameterWidth (level i.val))
    (fun i => dyadicParameterWidth_antitone i.property.le)
    (fun z hz => ht z (hRE hz)) (fun z hz => ⟨hcoeff z (hRE hz) 1,hcoeff z (hRE hz) 2⟩)
  let lists : I → (Fin 4 → ℤ) → (Fin 2 → ℤ) → Finset ℤ := fun i q v =>
    if hi : start ≤ level i then data.lists ⟨i,hi⟩ q v
    else coarse ⟨i,Nat.lt_of_not_ge hi⟩ (q,v)
  refine ⟨R,hR,hRE,hloss,⟨lists,?_,?_⟩⟩
  · intro i q v
    dsimp only [lists]
    split_ifs with hi
    · exact (data.card ⟨i,hi⟩ q v).trans (le_max_right _ _)
    · exact (hcoarse ⟨i,Nat.lt_of_not_ge hi⟩ (q,v)).trans (le_max_left _ _)
  · intro i z hz
    dsimp only [lists]
    split_ifs with hi
    · exact data.known ⟨i,hi⟩ z hz
    · exact hcoarseKnown ⟨i,Nat.lt_of_not_ge hi⟩ z hz

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
