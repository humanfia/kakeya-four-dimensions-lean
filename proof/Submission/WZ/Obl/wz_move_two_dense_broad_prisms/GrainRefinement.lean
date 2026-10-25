-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.GrainRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.BroadRefinement
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.FibreRetention
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.BrushSelection

/-! Passing the frozen old-grain geometry to a residual fibre refinement. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open wz_clustered_cover_volume_gain (fiberBodyCount fiberBodyCount_eq_ncard)

lemma supported_fibre_count {n N : ℕ} (f : Fin n → Fin N) (S : Finset (Fin n))
    (Z : Fin n → Set V) (hZ : ∀ i, i ∉ S → Z i = ∅) (k : Fin N) (p : V) :
    fiberBodyCount f Z k p = ({i | i ∈ S ∧ f i = k ∧ p ∈ Z i}.ncard : ℝ) := by
  rw [fiberBodyCount_eq_ncard]
  congr 2
  ext i
  constructor
  · rintro ⟨hfi, hp⟩
    have hi : i ∈ S := by
      by_contra hh
      simpa only [hZ i hh, mem_empty_iff_false] using hp
    exact ⟨hi, hfi, hp⟩
  · exact fun hi => ⟨hi.2.1, hi.2.2⟩

/-- The pointwise retention produced by preparation preserves broadness and
all occupied fibre lower bounds. -/
theorem retained_broad_and_level {n N : ℕ} {ω ζ d h ρ τ m : ℝ}
    {v : Fin n → V} {f : Fin n → Fin N} {S : Finset (Fin n)}
    {Z W : Fin n → Set V} (hd : 0 < d)
    (hZS : ∀ i, i ∉ S → Z i = ∅) (hWZ : ∀ i, W i ⊆ Z i)
    (hBr : Broad ω ζ d h ρ n N v S Z f)
    (hlevel : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) →
      m ≤ ({i | i ∈ S ∧ f i = k ∧ p ∈ Z i}.ncard : ℝ))
    (hretain : ∀ k p, (∃ i, f i = k ∧ p ∈ W i) →
      fiberBodyCount f Z k p ≤ 32*fiberBodyCount f W k p)
    (hbudget : 32 ≤ d^(-τ)) :
    Broad ω ζ d (h+τ) ρ n N v S W f ∧
      ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ W i) →
        m/32 ≤ ({i | i ∈ S ∧ f i = k ∧ p ∈ W i}.ncard : ℝ) := by
  have hWS : ∀ i, i ∉ S → W i = ∅ := by
    intro i hi
    exact subset_empty_iff.mp ((hWZ i).trans (by rw [hZS i hi]))
  have hcount : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ W i) →
      ({i | i ∈ S ∧ f i = k ∧ p ∈ Z i}.ncard : ℝ) ≤
      32*({i | i ∈ S ∧ f i = k ∧ p ∈ W i}.ncard : ℝ) := by
    rintro k p ⟨i, hiS, hfi, hp⟩
    have hh := hretain k p ⟨i, hfi, hp⟩
    simpa only [supported_fibre_count f S Z hZS, supported_fibre_count f S W hWS] using hh
  refine ⟨broad_of_retained_fibre_count hd hWZ hBr (fun k p hp =>
    (hcount k p hp).trans (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _))), ?_⟩
  intro k p hp
  obtain ⟨i, hiS, hfi, hpi⟩ := hp
  have hlow := hlevel k p ⟨i, hiS, hfi, hWZ i hpi⟩
  have hh := hcount k p ⟨i, hiS, hfi, hpi⟩
  linarith

/-- A shading refinement inherits grain membership and whole-tube crossing
from the frozen old-grain incidence clauses. -/
theorem refined_grain_geometry {n N J : ℕ} {d h ρ a c b g m : ℝ}
    {x v : Fin n → V} {S : Finset (Fin n)} {Z W : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin J → V} {e : Fin J → V ≃ₗᵢ[ℝ] V} {G : Fin J → Set V} {γ : Fin J → Fin N}
    (hHB : HB d h n x v S Z ρ N y w f a c b g J z e G γ m)
    (hZS : ∀ i, i ∉ S → Z i = ∅) (hWZ : ∀ i, W i ⊆ Z i) :
    (∀ i, (W i).Nonempty → i ∈ S) ∧
    (∀ j, G j ⊆ P a (ρ*c) c (z j) (e j)) ∧
    (∀ i p, p ∈ W i → ∃ j, f i = γ j ∧ p ∈ G j) ∧
    ∀ i j, f i = γ j → (W i ∩ G j).Nonempty →
      W i ∩ P a (ρ*c) c (z j) (e j) ⊆ G j ∧
      Crosses d a (ρ*c) c (x i) (v i) (z j) (e j) := by
  obtain ⟨hda, hab, hbc, hc1, hG, hdis, hcover, hmass, hlevel, hcross, hrest⟩ := hHB
  have hWS (i) (hi : (W i).Nonempty) : i ∈ S := by
    obtain ⟨p, hp⟩ := hi
    by_contra hnot
    have hpZ := hWZ i hp
    simpa only [hZS i hnot, mem_empty_iff_false] using hpZ
  refine ⟨hWS, fun j => (hG j).2.1, ?_, ?_⟩
  · intro i p hp
    have hiS := hWS i ⟨p, hp⟩
    have hh' : p ∈ {p | ∃ j, γ j = f i ∧ p ∈ G j} := by
      rw [hcover (f i)]
      exact ⟨i, hiS, rfl, hWZ i hp⟩
    obtain ⟨j, hji, hpj⟩ := hh'
    exact ⟨j, hji.symm, hpj⟩
  · intro i j hfi hmeet
    obtain ⟨p, hpW, hpG⟩ := hmeet
    have hh := hcross i (hWS i ⟨p, hpW⟩) j hfi ⟨p, hWZ i hpW, hpG⟩
    exact ⟨fun q hq => hh.1 ⟨hWZ i hq.1, hq.2⟩, hh.2⟩

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
