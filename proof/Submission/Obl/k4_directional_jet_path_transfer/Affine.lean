import Mathlib

open Metric Set

namespace Submission.Obl.k4_directional_jet_path_transfer

/-- The ordinary jet of an affine complex slice is the diagonal Fréchet jet. -/
lemma iteratedDeriv_affine_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) {H : E → ℂ}
    (hH : ContDiffOn ℂ ((⊤ : ENat) : WithTop ENat) H U)
    {p : E} (hp : p ∈ U) (v : E) (j : ℕ) :
    iteratedDeriv j (fun t : ℂ => H (p + t • v)) 0 =
      iteratedFDeriv ℂ j H p (fun _ => v) := by
  let g : E → ℂ := fun z => H (p + z)
  let W : Set E := (fun z : E => p + z) ⁻¹' U
  let T : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  have hW : IsOpen W := hU.preimage (by fun_prop)
  have hg : ContDiffOn ℂ ((⊤ : ENat) : WithTop ENat) g W :=
    hH.comp (by fun_prop) (fun z hz => hz)
  have hWT : IsOpen (T ⁻¹' W) := hW.preimage T.continuous
  have h0 : T 0 ∈ W := by simpa [T, W] using hp
  have hid := T.iteratedFDerivWithin_comp_right hg hW.uniqueDiffOn hWT.uniqueDiffOn
    h0 (i := j) (by exact_mod_cast (le_top : (j : ENat) ≤ ⊤))
  rw [iteratedFDerivWithin_of_isOpen j hWT h0,
    iteratedFDerivWithin_of_isOpen j hW h0] at hid
  have hshift : iteratedFDeriv ℂ j g (T 0) = iteratedFDeriv ℂ j H p := by
    simpa [g, T] using iteratedFDeriv_comp_add_left (𝕜 := ℂ) (f := H) j p 0
  rw [hshift] at hid
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℂ j (g ∘ T) 0 (fun _ => 1) = _
  rw [hid]
  simp [T]

lemma norm_iteratedDeriv_affine_slice_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) {H : E → ℂ}
    (hH : ContDiffOn ℂ ((⊤ : ENat) : WithTop ENat) H U)
    {p : E} (hp : p ∈ U) (v : E) (j : ℕ) :
    ‖iteratedDeriv j (fun t : ℂ => H (p + t • v)) 0‖ ≤
      ‖iteratedFDeriv ℂ j H p‖ * ‖v‖ ^ j := by
  rw [iteratedDeriv_affine_slice hU hH hp]
  simpa using (iteratedFDeriv ℂ j H p).le_opNorm (fun _ => v)

end Submission.Obl.k4_directional_jet_path_transfer
