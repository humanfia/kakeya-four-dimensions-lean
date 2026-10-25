-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainRefinementBroadness.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainRefinementBroadness.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from this workspace's o169/x0641, WangZahlLot/Obl/wz_move_three_wide_grains_core/GrainRefinementBroadness.lean
   (7d05c80, sessions x0450/x0641/x0670). Namespace and grain-witness interface adjusted. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.TwoScaleBroadness
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainComponents
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainAxes
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open scoped Classical
open WangZahlLot.Obl.wz_measurable_angular_selection (pd pd_comm pd_triangle)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis)

/-- Pull a refinement of the old grain shadings back to all fine incidences
of its old coarse fibre. -/
def grainFineRefinement {n N L : ℕ} (S : Finset (Fin n)) (Z : Fin n → Set V)
    (f : Fin n → Fin N) (W : Fin L → Set V) (γ : Fin L → Fin N)
    (i : Fin n) : Set V := ⋃ j, grainComponent S Z f W γ j i

theorem mem_grainFineRefinement {n N L : ℕ} (S : Finset (Fin n))
    (Z : Fin n → Set V) (f : Fin n → Fin N) (W : Fin L → Set V)
    (γ : Fin L → Fin N) (i : Fin n) (p : V) :
    p ∈ grainFineRefinement S Z f W γ i ↔
      i ∈ S ∧ p ∈ Z i ∧ ∃ j, γ j = f i ∧ p ∈ W j := by
  simp only [grainFineRefinement, mem_iUnion, grainComponent, mem_ofPred_eq, mem_inter_iff]
  constructor
  · rintro ⟨j, hi, hf, hp, hj⟩
    exact ⟨hi, hp, j, hf.symm, hj⟩
  · rintro ⟨hi, hp, j, hf, hj⟩
    exact ⟨j, hi, hf.symm, hp, hj⟩

/-- With the original support convention this is the fibre restriction used
by the accepted grain-refinement mass transfer. -/
theorem grainFineRefinement_eq_assignedFiber {n N L : ℕ} (S : Finset (Fin n))
    (Z : Fin n → Set V) (f : Fin n → Fin N) (W : Fin L → Set V)
    (γ : Fin L → Fin N) (hsupport : ∀ i, i ∉ S → Z i = ∅) (i : Fin n) :
    grainFineRefinement S Z f W γ i =
      Z i ∩ WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber γ W (f i) := by
  ext p
  rw [mem_grainFineRefinement]
  constructor
  · exact fun hp => ⟨hp.2.1, hp.2.2⟩
  · rintro ⟨hp, hj⟩
    refine ⟨?_, hp, hj⟩
    by_contra hi
    simp only [hsupport i hi, mem_empty_iff_false] at hp

/-- Common spatial cuts on the grain rows induce the same common cut on
all their fine incidences. -/
theorem grainFineRefinement_common_cut {n N L : ℕ} (S : Finset (Fin n))
    (Z : Fin n → Set V) (f : Fin n → Fin N) (W : Fin L → Set V)
    (γ : Fin L → Fin N) (D : Set V) (i : Fin n) :
    grainFineRefinement S Z f (fun j => W j ∩ D) γ i =
      grainFineRefinement S Z f W γ i ∩ D := by
  ext p
  simp only [mem_grainFineRefinement, mem_inter_iff]
  constructor
  · rintro ⟨hi, hp, j, hj, hjW, hpD⟩
    exact ⟨⟨hi, hp, j, hj, hjW⟩, hpD⟩
  · rintro ⟨⟨hi, hp, j, hj, hjW⟩, hpD⟩
    exact ⟨hi, hp, j, hj, hjW, hpD⟩

/-- Auxiliary grain directions close to the original coarse directions
transfer their broadness to fine incidences. This also supports affine maps
whose normalized old axes change by only a fixed multiple of the old radius. -/
theorem grain_refinement_fine_broad_of_close {ω ζ δ h ρ θ a c b g m B A₀ r₀ : ℝ}
    {n N L : ℕ} {x v : Fin n → V} {Y Z : Fin n → Set V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {Hs W : Fin L → Set V} {γ : Fin L → Fin N} {ν : Fin L → V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h) (hδρ : δ ≤ ρ)
    (hθ : 0 < θ) (hβ : 0 ≤ ω * ζ / 100) (hB : 0 ≤ B) (hm : 0 ≤ m)
    (hv : ∀ i, ‖v i‖ = 1)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ h ρ n N v S Z f)
    (hHB : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hs γ m)
    (hW : ∀ j, W j ⊆ Hs j)
    (hA₀ : 1 ≤ A₀) (hcut : r₀ ≤ (A₀ + 1) * ρ)
    (hcloseAxis : ∀ j, (W j).Nonempty → pd (ν j) (w (γ j)) ≤ A₀ * ρ)
    (haxis : ∀ p u r, ‖u‖ = 1 → r₀ ≤ r →
      q L {j | p ∈ W j ∧ pd (ν j) u ≤ r} ≤
        B * (r / θ) ^ (ω * ζ / 100) * q L {j | p ∈ W j}) :
    ∀ p u r, ‖u‖ = 1 → δ ≤ r →
      q n {i | p ∈ grainFineRefinement S Z f W γ i ∧ pd (v i) u ≤ r} ≤
        (2 * δ ^ (-h) * B * (5 * (A₀ + 1)) ^ (ω * ζ / 100)) *
          (r / θ) ^ (ω * ζ / 100) *
            q n {i | p ∈ grainFineRefinement S Z f W γ i} := by
  classical
  intro p u r hu hr
  let F := Finset.univ.filter (fun i => p ∈ grainFineRefinement S Z f W γ i)
  let J := Finset.univ.filter (fun j => p ∈ W j)
  let K := J.image γ
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hJ (j : Fin L) : j ∈ J ↔ p ∈ W j := by simp [J]
  have hK (k : Fin N) : k ∈ K ↔ ∃ j, γ j = k ∧ p ∈ W j := by
    simp only [K, Finset.mem_image, hJ]
    aesop
  have hF (i : Fin n) : i ∈ F ↔ i ∈ S ∧ p ∈ Z i ∧ f i ∈ K := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_grainFineRefinement, hK]
  have hmap : ∀ i ∈ F, f i ∈ K := fun i hi => ((hF i).mp hi).2.2
  have hfilter (k : Fin N) (hk : k ∈ K) :
      F.filter (fun i => f i = k) =
        Finset.univ.filter (fun i => i ∈ S ∧ f i = k ∧ p ∈ Z i) := by
    ext i
    simp only [Finset.mem_filter, hF, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hi, hp, _⟩, hf⟩
      exact ⟨hi, hf, hp⟩
    · rintro ⟨hi, hf, hp⟩
      exact ⟨⟨hi, hp, hf ▸ hk⟩, hf⟩
  have hcard (k : Fin N) (hk : k ∈ K) :
      ((F.filter (fun i => f i = k)).card : ℝ) =
        q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} := by
    rw [hfilter k hk]
    simp [q, Set.ncard_eq_toFinset_card']
  have hlevel (k : Fin N) (hk : k ∈ K) :
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} ∈ Icc m (2 * m) := by
    apply hHB.2.2.2.2.2.2.2.2.1
    obtain ⟨j, hj, hp⟩ := (hK k).mp hk
    have hp' : p ∈ {p | ∃ j, γ j = k ∧ p ∈ Hs j} := ⟨j, hj, hW j hp⟩
    rw [hHB.2.2.2.2.2.2.1] at hp'
    exact hp'
  have hlower (k : Fin N) (hk : k ∈ K) :
      m ≤ ((F.filter (fun i => f i = k)).card : ℝ) := by
    rw [hcard k hk]
    exact (hlevel k hk).1
  have hupper (k : Fin N) (hk : k ∈ K) :
      ((F.filter (fun i => f i = k)).card : ℝ) ≤ 2 * m := by
    rw [hcard k hk]
    exact (hlevel k hk).2
  have hclose (i : Fin n) (hi : i ∈ F) : pd (v i) (w (f i)) ≤ 4 * ρ :=
    (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.pd_lt_of_tube_subset
      hδ (hv i) (hC.2.2.1 (f i)) (hC.2.2.2.1 i ((hF i).mp hi).1)).le
  have hfine (k : Fin N) (hk : k ∈ K) (u : V) (r : ℝ)
      (hu : ‖u‖ = 1) (hr : δ ≤ r) (hrρ : r ≤ ρ) :
      ((F.filter (fun i => f i = k ∧ pd (v i) u ≤ r)).card : ℝ) ≤
        δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) *
          (F.filter (fun i => f i = k)).card := by
    have he : F.filter (fun i => f i = k ∧ pd (v i) u ≤ r) =
        (F.filter (fun i => f i = k)).filter (fun i => pd (v i) u ≤ r) := by
      simp [Finset.filter_filter]
    rw [he, hfilter k hk]
    simpa [pd, q, Set.ncard_eq_toFinset_card', Finset.filter_filter, and_assoc] using
      hbr k p u r hu hr hrρ
  have hinj : Set.InjOn γ (J : Set (Fin L)) := by
    intro j hj k hk he
    by_contra hne
    exact Set.disjoint_left.mp (hHB.2.2.2.2.2.1 j k hne he)
      (hW j ((hJ j).mp hj)) (hW k ((hJ k).mp hk))
  have hcardK : K.card = J.card := Finset.card_image_iff.mpr hinj
  have hcoarse (u : V) (R : ℝ) (hu : ‖u‖ = 1) (hR : ρ ≤ R) :
      ((K.filter (fun k => pd (w k) u ≤ R)).card : ℝ) ≤
        (B * (A₀ + 1) ^ (ω * ζ / 100)) * (R / θ) ^ (ω * ζ / 100) * K.card := by
    have hsub : K.filter (fun k => pd (w k) u ≤ R) ⊆
        (J.filter (fun j => pd (ν j) u ≤ (A₀ + 1) * R)).image γ := by
      intro k hk
      obtain ⟨hkK, hku⟩ := Finset.mem_filter.mp hk
      obtain ⟨j, hj, hp⟩ := (hK k).mp hkK
      refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨(hJ j).mpr hp, ?_⟩, hj⟩
      have ha := hcloseAxis j ⟨p, hp⟩
      have ht := pd_triangle (ν j) (w (γ j)) u
      rw [hj] at ha ht
      have hh := mul_le_mul_of_nonneg_left hR (zero_le_one.trans hA₀)
      linarith only [ha, ht, hku, hh]
    have hcap : ((J.filter (fun j => pd (ν j) u ≤ (A₀ + 1) * R)).card : ℝ) ≤
        B * (((A₀ + 1) * R) / θ) ^ (ω * ζ / 100) * J.card := by
      simpa only [J, q, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred,
        Finset.filter_filter] using haxis p u ((A₀ + 1) * R) hu
          (hcut.trans (mul_le_mul_of_nonneg_left hR (by linarith : 0 ≤ A₀ + 1)))
    have he : (((A₀ + 1) * R) / θ) ^ (ω * ζ / 100) =
        (A₀ + 1) ^ (ω * ζ / 100) * (R / θ) ^ (ω * ζ / 100) := by
      rw [show ((A₀ + 1) * R) / θ = (A₀ + 1) * (R / θ) by ring,
        Real.mul_rpow (by linarith : (0 : ℝ) ≤ A₀ + 1) (div_nonneg (hρ.le.trans hR) hθ.le)]
    calc
      _ ≤ ((J.filter (fun j => pd (ν j) u ≤ (A₀ + 1) * R)).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_image_le)
      _ ≤ _ := hcap
      _ = _ := by rw [he, hcardK]; ring
  have H := two_scale_broadness v w F K f hδ hδρ hθ hβ (by norm_num : (0 : ℝ) ≤ 4)
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith : -h ≤ 0))
    (by positivity : 0 ≤ B * (A₀ + 1) ^ (ω * ζ / 100)) hm (by norm_num : (0 : ℝ) ≤ 2)
    hmap hlower hupper hclose hfine hcoarse u r hu hr
  have he : (2 * δ ^ (-h) * (B * (A₀ + 1) ^ (ω * ζ / 100)) *
      ((4 : ℝ) + 1) ^ (ω * ζ / 100)) =
      2 * δ ^ (-h) * B * (5 * (A₀ + 1)) ^ (ω * ζ / 100) := by
    rw [show (4 : ℝ) + 1 = 5 by norm_num,
      show (5 * (A₀ + 1)) = (A₀ + 1) * 5 by ring,
      Real.mul_rpow (by linarith : (0 : ℝ) ≤ A₀ + 1) (by norm_num : (0 : ℝ) ≤ 5)]
    ring
  rw [he] at H
  simpa only [F, q, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred,
    Finset.filter_filter] using H

/-- Directional broadness of retained physical grain axes transfers directly
to their fine incidences. Only the original coarse cover is used. -/
theorem grain_refinement_fine_broad {ω ζ δ h ρ θ a c b g m B : ℝ}
    {n N L : ℕ} {x v : Fin n → V} {Y Z : Fin n → Set V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {Hs W : Fin L → Set V} {γ : Fin L → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h) (hδρ : δ ≤ ρ)
    (hθ : 0 < θ) (hβ : 0 ≤ ω * ζ / 100) (hB : 0 ≤ B) (hm : 0 ≤ m)
    (hv : ∀ i, ‖v i‖ = 1)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ h ρ n N v S Z f)
    (hHB : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hs γ m)
    (hW : ∀ j, W j ⊆ Hs j)
    (haxis : ∀ p u r, ‖u‖ = 1 → 2 * ρ ≤ r →
      q L {j | p ∈ W j ∧ pd (boxAxis (e j) 2) u ≤ r} ≤
        B * (r / θ) ^ (ω * ζ / 100) * q L {j | p ∈ W j}) :
    ∀ p u r, ‖u‖ = 1 → δ ≤ r →
      q n {i | p ∈ grainFineRefinement S Z f W γ i ∧ pd (v i) u ≤ r} ≤
        (2 * δ ^ (-h) * B * (105 : ℝ) ^ (ω * ζ / 100)) *
          (r / θ) ^ (ω * ζ / 100) *
            q n {i | p ∈ grainFineRefinement S Z f W γ i} := by
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hclose j (_ : (W j).Nonempty) :
      pd (boxAxis (e j) 2) (w (γ j)) ≤ 20 * ρ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.grain_axis_close hρ.le
      (e j) (hC.2.2.1 (γ j)) (hHB.2.2.2.2.1 j).2.2.2
  simpa only [show (5 : ℝ) * (20 + 1) = 105 by norm_num] using
    grain_refinement_fine_broad_of_close hδ hδ1 hh hδρ hθ hβ hB hm hv hC hbr hHB hW
      (by norm_num : (1 : ℝ) ≤ 20) (by nlinarith : 2 * ρ ≤ (20 + 1) * ρ) hclose haxis

/-- The affine packet directions may be expressed in a common rotated
frame. An additive angular error on each occupied old grain is sufficient. -/
theorem grain_refinement_fine_broad_in_frame {ω ζ δ h ρ θ a c b g m B C₀ : ℝ}
    {n N L : ℕ} {x v : Fin n → V} {Y Z : Fin n → Set V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {Hs W : Fin L → Set V} {γ : Fin L → Fin N} {ν : Fin L → V}
    (R : V ≃ₗᵢ[ℝ] V)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h) (hδρ : δ ≤ ρ)
    (hθ : 0 < θ) (hβ : 0 ≤ ω * ζ / 100) (hB : 0 ≤ B) (hm : 0 ≤ m)
    (hC₀ : 0 ≤ C₀) (hv : ∀ i, ‖v i‖ = 1)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ h ρ n N v S Z f)
    (hHB : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hs γ m)
    (hW : ∀ j, W j ⊆ Hs j)
    (hclose : ∀ j, (W j).Nonempty → pd (ν j) (R (boxAxis (e j) 2)) ≤ C₀ * ρ)
    (haxis : ∀ p u r, ‖u‖ = 1 → 2 * ρ ≤ r →
      q L {j | p ∈ W j ∧ pd (ν j) u ≤ r} ≤
        B * (r / θ) ^ (ω * ζ / 100) * q L {j | p ∈ W j}) :
    ∀ p u r, ‖u‖ = 1 → δ ≤ r →
      q n {i | p ∈ grainFineRefinement S Z f W γ i ∧ pd (v i) u ≤ r} ≤
        (2 * δ ^ (-h) * B * (5 * (C₀ + 21)) ^ (ω * ζ / 100)) *
          (r / θ) ^ (ω * ζ / 100) *
            q n {i | p ∈ grainFineRefinement S Z f W γ i} := by
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hiso (u v : V) : pd (R u) (R v) = pd u v :=
    WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd_isometry R u v
  have hpd (j : Fin L) (u : V) : pd (R.symm (ν j)) u = pd (ν j) (R u) := by
    simpa only [R.apply_symm_apply] using (hiso (R.symm (ν j)) u).symm
  have hclose' j (hj : (W j).Nonempty) :
      pd (R.symm (ν j)) (w (γ j)) ≤ (C₀ + 20) * ρ := by
    rw [hpd]
    have ha : pd (boxAxis (e j) 2) (w (γ j)) ≤ 20 * ρ :=
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.grain_axis_close hρ.le
        (e j) (hC.2.2.1 (γ j)) (hHB.2.2.2.2.1 j).2.2.2
    have ht := pd_triangle (ν j) (R (boxAxis (e j) 2)) (R (w (γ j)))
    rw [hiso] at ht
    linarith only [ht, ha, hclose j hj]
  have haxis' (p u : V) (r : ℝ) (hu : ‖u‖ = 1) (hr : 2 * ρ ≤ r) :
      q L {j | p ∈ W j ∧ pd (R.symm (ν j)) u ≤ r} ≤
        B * (r / θ) ^ (ω * ζ / 100) * q L {j | p ∈ W j} := by
    simp_rw [hpd]
    exact haxis p (R u) r (by simpa only [R.norm_map] using hu) hr
  simpa only [show C₀ + 20 + 1 = C₀ + 21 by ring] using
    grain_refinement_fine_broad_of_close hδ hδ1 hh hδρ hθ hβ hB hm hv hC hbr hHB hW
      (by linarith : 1 ≤ C₀ + 20) (by nlinarith : 2 * ρ ≤ (C₀ + 20 + 1) * ρ)
      hclose' haxis'

/-- The direct grain-to-fine transfer in the frozen broadness format,
with the precise cost of changing the packet scale to the prism scale. -/
theorem grain_refinement_broad_clause {ω ζ δ h h' ρ ρ' θ a c b g m B : ℝ}
    {n N L : ℕ} {x v : Fin n → V} {Y Z : Fin n → Set V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {Hs W : Fin L → Set V} {γ : Fin L → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h) (hδρ : δ ≤ ρ)
    (hθ : 0 < θ) (hρ' : 0 < ρ') (hβ : 0 ≤ ω * ζ / 100)
    (hB : 0 ≤ B) (hm : 0 ≤ m) (hv : ∀ i, ‖v i‖ = 1)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ h ρ n N v S Z f)
    (hHB : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hs γ m)
    (hW : ∀ j, W j ⊆ Hs j)
    (haxis : ∀ p u r, ‖u‖ = 1 → 2 * ρ ≤ r →
      q L {j | p ∈ W j ∧ pd (boxAxis (e j) 2) u ≤ r} ≤
        B * (r / θ) ^ (ω * ζ / 100) * q L {j | p ∈ W j})
    (hbudget : 2 * δ ^ (-h) * B * (105 : ℝ) ^ (ω * ζ / 100) *
      (ρ' / θ) ^ (ω * ζ / 100) ≤ δ ^ (-h')) :
    ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ' →
      q n {i | p ∈ grainFineRefinement S Z f W γ i ∧
        min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
      δ ^ (-h') * (r / ρ') ^ (ω * ζ / 100) *
        q n {i | p ∈ grainFineRefinement S Z f W γ i} := by
  intro p u r hu hr _
  have H := grain_refinement_fine_broad hδ hδ1 hh hδρ hθ hβ hB hm hv
    hC hbr hHB hW haxis p u r hu hr
  have hr0 : 0 ≤ r := hδ.le.trans hr
  have he : (r / θ) ^ (ω * ζ / 100) =
      (ρ' / θ) ^ (ω * ζ / 100) * (r / ρ') ^ (ω * ζ / 100) := by
    rw [← Real.mul_rpow (div_nonneg hρ'.le hθ.le) (div_nonneg hr0 hρ'.le)]
    congr 1
    field_simp
  rw [he] at H
  have H' : q n {i | p ∈ grainFineRefinement S Z f W γ i ∧ pd (v i) u ≤ r} ≤
      (2 * δ ^ (-h) * B * (105 : ℝ) ^ (ω * ζ / 100) *
        (ρ' / θ) ^ (ω * ζ / 100)) * (r / ρ') ^ (ω * ζ / 100) *
          q n {i | p ∈ grainFineRefinement S Z f W γ i} := by
    convert H using 1
    ring
  exact H'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (div_nonneg hr0 hρ'.le) _))
    (Nat.cast_nonneg _))

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
