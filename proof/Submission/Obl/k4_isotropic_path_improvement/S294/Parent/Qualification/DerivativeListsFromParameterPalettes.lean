-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.DerivativeListsFromParameterPalettes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalStateCanonicalMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterPalette2

/-! Actual scalar derivative lists from the prepared coefficient
palettes. All intermediate cells and coefficient worlds are enumerated
here, with an explicit polynomial cost in their original bounds. -/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set

noncomputable section

/-- Canonical parameter palettes give ordinary-cell derivative lists.
Every listed derivative bin is controlled by an original coefficient
bin and the actual time cell; there is no derivative-list oracle. -/
theorem derivative_lists_of_canonical_parameter_palettes {Λ : Type*}
    (E : Set (Λ × ℝ)) (c : Λ → Fin 7 → ℝ)
    {s H V P : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hH : 0 ≤ H)
    (_hV : 0 ≤ V) (hP : 0 ≤ P)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1) (hc2 : ∀ z∈E, |c z.1 2| ≤ H)
    (worlds : Finset (Fin 7 → ℤ))
    (hworlds : ∀ z∈E, parameterCode 1 (c z.1)∈worlds)
    (menus : ((Fin 4 → ℤ) × (Fin 7 → ℤ)) → Finset (Fin 4 → ℤ))
    (hmenu : ∀ key, ((menus key).card : ℝ) ≤ V)
    (hmenuKnown : ∀ z∈E, canonicalZoomCell c 1 s z∈
      menus (originalFineState c s z,parameterCode 1 (c z.1)))
    (palettes : (((Fin 7 → ℤ) × (Fin 4 → ℤ)) × (Fin 2 → ℤ)) → Finset (Fin 7 → ℤ))
    (hpalettes : ∀ key, ((palettes key).card : ℝ) ≤ P)
    (hknown : ∀ z∈E, parameterCode s (c z.1)∈
      palettes ((parameterCode 1 (c z.1),canonicalZoomCell c 1 s z),
        parameterCode s (zv (c z.1)))) :
    ∃ lists : ((Fin 4 → ℤ) × (Fin 2 → ℤ)) → Finset ℤ,
      (∀ key, ((lists key).card : ℝ) ≤
        (worlds.card:ℝ)*V*P*(2*(⌈2*H+5⌉:ℝ)+1)) ∧
      ∀ z∈E, ⌊(c z.1 1+2*c z.1 2*z.2)/s⌋∈
        lists (originalFineState c s z,parameterCode s (zv (c z.1))) := by
  classical
  let params := fun key : (Fin 4 → ℤ) × (Fin 2 → ℤ) =>
    worlds.biUnion fun world =>
      (menus (key.1,world)).biUnion fun cell => palettes ((world,cell),key.2)
  have hparams (key) : ((params key).card : ℝ) ≤ (worlds.card:ℝ)*V*P := by
    have hinner (world : Fin 7 → ℤ) :
        (((menus (key.1,world)).biUnion fun cell => palettes ((world,cell),key.2)).card:ℝ) ≤ V*P := by
      calc
        _ ≤ ∑ cell∈menus (key.1,world), ((palettes ((world,cell),key.2)).card:ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _cell∈menus (key.1,world), P :=
          Finset.sum_le_sum fun cell _ => hpalettes _
        _ = ((menus (key.1,world)).card:ℝ)*P := by simp only [Finset.sum_const,nsmul_eq_mul]
        _ ≤ V*P := mul_le_mul_of_nonneg_right (hmenu _) hP
    calc
      _ ≤ ∑ world∈worlds,
          (((menus (key.1,world)).biUnion fun cell => palettes ((world,cell),key.2)).card:ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _world∈worlds, V*P := Finset.sum_le_sum fun world _ => hinner world
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hparamKnown (z : Λ × ℝ) (hz : z∈E) :
      parameterCode s (c z.1)∈params
        (originalFineState c s z,parameterCode s (zv (c z.1))) :=
    Finset.mem_biUnion.mpr ⟨_,hworlds z hz,
      Finset.mem_biUnion.mpr ⟨_,hmenuKnown z hz,hknown z hz⟩⟩
  let R : ℤ := ⌈2*H+5⌉
  have hR0 : 0 ≤ R := by
    have hh := Int.le_ceil (2*H+5)
    exact_mod_cast (show (0:ℝ) ≤ (R:ℝ) by dsimp only [R]; linarith only [hh,hH])
  let center := fun (key : (Fin 4 → ℤ) × (Fin 2 → ℤ)) (fine : Fin 7 → ℤ) =>
    ⌊(s*(fine 1:ℝ)+2*(s*(fine 2:ℝ))*(s*(key.1 0:ℝ)))/s⌋
  let interval := fun key fine => Finset.Icc (center key fine-R) (center key fine+R)
  have hinterval (key) (fine : Fin 7 → ℤ) :
      ((interval key fine).card:ℝ)=2*(R:ℝ)+1 := by
    simp only [interval,Int.card_Icc]
    have he : center key fine+R+1-(center key fine-R)=2*R+1 := by ring
    rw [he,←Int.cast_natCast,Int.toNat_of_nonneg (by omega)]
    push_cast
    ring
  let lists := fun key => (params key).biUnion (interval key)
  refine ⟨lists,?_,?_⟩
  · intro key
    calc
      _ ≤ ∑ fine∈params key, ((interval key fine).card:ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ = ((params key).card:ℝ)*(2*(R:ℝ)+1) := by
        simp only [hinterval,Finset.sum_const,nsmul_eq_mul]
      _ ≤ ((worlds.card:ℝ)*V*P)*(2*(R:ℝ)+1) :=
        mul_le_mul_of_nonneg_right (hparams key) (by positivity)
      _ = _ := rfl
  · intro z hz
    apply Finset.mem_biUnion.mpr
    refine ⟨parameterCode s (c z.1),hparamKnown z hz,?_⟩
    exact derivative_bins_of_block hs hs1 hH (parameterCode s (c z.1))
      (originalFineState c s z 0) rfl (hc2 z hz) rfl (ht z hz)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
