-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.Cut
import Submission.Obl.k4_finite_affine_parent_sources.LabelledStage
import Submission.Obl.k4_finite_affine_parent_sources.SourceCoordinates
import Submission.Obl.k4_finite_affine_parent_sources.ModelEH1

/-!
# The source stage of a prepared parent

A `SourceData` record fixes one parent label of the original path, a spatial frame `D₀` for
it, the model loss `K`, the velocity palette `π`, the prepared incidence set `S` (in the
parent's world), the original level `depth s` used for each model depth `s`, and tracking
coefficients for the model labels. `SourceData.stage` is the induced model of `E`: the
parent prior conditioned on the full parent assignment, the parent-time normalized prepared
incidences (`muE`), the parent normalization of all coefficients (`affineSourceFrame`, no
hidden correction), the normalized parent test, and as labels the actual old labels at level
`depth s` met by `S`, with their full assignments and relative dyadic blocks.

Written by x0891 for o232 (assembly of SourcePreparation, coordinated with x0807).
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open Submission.Obl.k4_finite_forest_width_selection

noncomputable section

/-- A residual family carried by one world only. -/
def worldOnly {W : ℕ} (w₀ : Fin W) (S : Set Incidence) : Fin W → Set Incidence :=
  fun w => if w = w₀ then S else ∅

/-- The choices defining one source stage. -/
structure SourceData {W : ℕ} (p : PathData W) where
  parent : Fin p.C
  D₀ : Matrix (Fin 2) (Fin 2) ℝ
  K : ℝ
  π : Measure ℝ
  S : Set Incidence
  depth : ℝ → ℕ
  c : (s : ℝ) → Fin (p.activeCount (worldOnly (p.world parent) S) (depth s)) → Fin 5 → ℝ

namespace SourceData

variable {W : ℕ} {p : PathData W} (D : SourceData p)

/-- The parent world. -/
def w₀ : Fin W := p.world D.parent

/-- The parent level. -/
def i₀ : ℕ := p.lev D.parent

/-- The parent block start. -/
def t₀ : ℝ := (p.bin D.parent : ℝ) / (2 : ℝ) ^ p.T D.i₀

/-- The parent block length. -/
def q₀ : ℝ := ((2 : ℝ) ^ p.T D.i₀)⁻¹

/-- The residual family whose met labels are the model labels. -/
def Hm : Fin W → Set Incidence := worldOnly D.w₀ D.S

/-- The actual old label behind a model label. -/
def old (s : ℝ) (i : Fin (p.activeCount D.Hm (D.depth s))) : Fin p.C :=
  p.activeLabel D.Hm (D.depth s) i

/-- The parent normalization (no hidden correction). -/
def frame (Nk : ℝ) (B : Fin W → ℝ) : PFrame :=
  affineSourceFrame D.t₀ D.q₀ (B D.w₀ / δ Nk (p.r D.i₀)) (p.center D.parent)
    (p.velocity D.parent) D.D₀

/-- Relative time exponent of a model depth. -/
def relT (s : ℝ) : ℕ := p.T (D.depth s) - p.T D.i₀

/-- Relative dyadic block of a model label. -/
def relBin (s : ℝ) (i : Fin (p.activeCount D.Hm (D.depth s))) : Fin (2 ^ D.relT s) :=
  ⟨p.bin (D.old s i) % 2 ^ D.relT s, Nat.mod_lt _ (by positivity)⟩

/-- The model of the source stage. -/
def stage (Nk L unit : ℝ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ) :
    EStage Trajectory where
  N := Nk ^ (unit * L)
  K := D.K
  ν := nuE (ν D.w₀) (p.assigned D.parent)
  μ := muE (ν D.w₀) (p.assigned D.parent) D.t₀ D.q₀ D.S
  ρ := muE (ν D.w₀) (p.assigned D.parent) D.t₀ D.q₀ D.S
  π := D.π
  b := (D.frame Nk B).eb
  P := (D.frame Nk B).normTest (δ Nk (p.r D.i₀)) (p.test D.parent)
  T := D.relT
  nl := fun s => p.activeCount D.Hm (D.depth s)
  j := D.relBin
  A := fun s i => p.assigned (D.old s i)
  B := fun s i => p.assigned (D.old s i)
  c := D.c
  F := fun s i => (D.frame Nk B).normTest (δ Nk (p.r D.i₀)) (p.test (D.old s i))

theorem old_level (s : ℝ) (i : Fin (p.activeCount D.Hm (D.depth s))) :
    p.lev (D.old s i) = D.depth s := p.activeLabel_level D.Hm (D.depth s) i

/-- Model labels live in the parent world and meet the prepared set. -/
theorem old_world (s : ℝ) (i : Fin (p.activeCount D.Hm (D.depth s))) :
    p.world (D.old s i) = D.w₀ ∧ (D.S ∩ p.counted (D.old s i)).Nonempty := by
  have h : (D.Hm (p.world (D.old s i)) ∩ p.counted (D.old s i)).Nonempty :=
    p.activeLabel_nonempty D.Hm (D.depth s) i
  by_cases hw : p.world (D.old s i) = D.w₀
  · refine ⟨hw, ?_⟩
    have hH : D.Hm (p.world (D.old s i)) = D.S := by
      simp only [Hm, worldOnly, hw, ite_true]
    rwa [hH] at h
  · exfalso
    have hH : D.Hm (p.world (D.old s i)) = ∅ := by
      simp only [Hm, worldOnly, hw, ite_false]
    rw [hH, Set.empty_inter] at h
    exact Set.not_nonempty_empty h

/-- A dyadic sub-block inside an enclosing block has the enclosing index as quotient. -/
theorem relative_block_div {T₀ T₁ : ℕ} (hT : T₀ ≤ T₁) {j₀ j₁ : ℕ}
    (hlo : (j₀ : ℝ) / (2 : ℝ) ^ T₀ ≤ (j₁ : ℝ) / (2 : ℝ) ^ T₁)
    (hhi : ((j₁ : ℝ) + 1) / (2 : ℝ) ^ T₁ ≤ ((j₀ : ℝ) + 1) / (2 : ℝ) ^ T₀) :
    j₁ / 2 ^ (T₁ - T₀) = j₀ := by
  set D := T₁ - T₀ with hD
  have h2T₁ : (2 : ℝ) ^ T₁ = (2 : ℝ) ^ T₀ * (2 : ℝ) ^ D := by
    rw [← pow_add, hD, Nat.add_sub_cancel' hT]
  have hA : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  have hlo' : (j₀ : ℝ) * (2 : ℝ) ^ D ≤ j₁ := by
    rw [h2T₁, div_le_div_iff₀ hA (by positivity)] at hlo
    nlinarith
  have hhi' : (j₁ : ℝ) + 1 ≤ ((j₀ : ℝ) + 1) * (2 : ℝ) ^ D := by
    rw [h2T₁, div_le_div_iff₀ (by positivity) hA] at hhi
    nlinarith
  have hlo'' : j₀ * 2 ^ D ≤ j₁ := by exact_mod_cast hlo'
  have hhi'' : j₁ + 1 ≤ (j₀ + 1) * 2 ^ D := by exact_mod_cast hhi'
  apply le_antisymm
  · have : j₁ < (j₀ + 1) * 2 ^ D := by omega
    have := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ D)).mpr this
    omega
  · exact (Nat.le_div_iff_mul_le (by positivity)).mpr hlo''

/-- A dyadic sub-block written in the time unit of an enclosing block. -/
theorem relative_block_mem {T₀ T₁ : ℕ} (hT : T₀ ≤ T₁) {j₀ j₁ : ℕ}
    (hlo : (j₀ : ℝ) / (2 : ℝ) ^ T₀ ≤ (j₁ : ℝ) / (2 : ℝ) ^ T₁)
    (hhi : ((j₁ : ℝ) + 1) / (2 : ℝ) ^ T₁ ≤ ((j₀ : ℝ) + 1) / (2 : ℝ) ^ T₀) (t : ℝ) :
    t ∈ Icc ((j₁ : ℝ) / (2 : ℝ) ^ T₁) (((j₁ : ℝ) + 1) / (2 : ℝ) ^ T₁) ↔
      (t - (j₀ : ℝ) / (2 : ℝ) ^ T₀) / ((2 : ℝ) ^ T₀)⁻¹ ∈
        IS (T₁ - T₀) ⟨j₁ % 2 ^ (T₁ - T₀), Nat.mod_lt _ (by positivity)⟩ := by
  set D := T₁ - T₀ with hD
  have h2T₁ : (2 : ℝ) ^ T₁ = (2 : ℝ) ^ T₀ * (2 : ℝ) ^ D := by
    rw [← pow_add, hD, Nat.add_sub_cancel' hT]
  have hA : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  have hB : (0 : ℝ) < (2 : ℝ) ^ D := by positivity
  -- integer form of the nesting
  have hlo' : (j₀ : ℝ) * (2 : ℝ) ^ D ≤ j₁ := by
    rw [h2T₁, div_le_div_iff₀ hA (by positivity)] at hlo
    nlinarith
  have hhi' : (j₁ : ℝ) + 1 ≤ ((j₀ : ℝ) + 1) * (2 : ℝ) ^ D := by
    rw [h2T₁, div_le_div_iff₀ (by positivity) hA] at hhi
    nlinarith
  have hlo'' : j₀ * 2 ^ D ≤ j₁ := by exact_mod_cast hlo'
  have hhi'' : j₁ + 1 ≤ (j₀ + 1) * 2 ^ D := by exact_mod_cast hhi'
  have hq : j₁ / 2 ^ D = j₀ := by
    apply le_antisymm
    · have : j₁ < (j₀ + 1) * 2 ^ D := by omega
      have := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ D)).mpr this
      omega
    · exact (Nat.le_div_iff_mul_le (by positivity)).mpr hlo''
  have hdecomp : (j₁ : ℝ) = (j₀ : ℝ) * (2 : ℝ) ^ D + ((j₁ % 2 ^ D : ℕ) : ℝ) := by
    have h := Nat.div_add_mod j₁ (2 ^ D)
    rw [hq] at h
    have : (j₁ : ℝ) = ((2 ^ D * j₀ + j₁ % 2 ^ D : ℕ) : ℝ) := by rw [h]
    rw [this]; push_cast; ring
  simp only [IS, Set.mem_Icc]
  have key : (t - (j₀ : ℝ) / (2 : ℝ) ^ T₀) / ((2 : ℝ) ^ T₀)⁻¹ =
      t * (2 : ℝ) ^ T₀ - j₀ := by
    field_simp
  rw [key, h2T₁]
  rw [div_le_iff₀ (by positivity), le_div_iff₀ (by positivity),
    div_le_iff₀ hB, le_div_iff₀ hB]
  rw [hdecomp]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

section Descendants

variable {m Mp Dp : ℕ} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- If the prepared set lies in the open parent block, every model label below the
parent level descends from the parent. -/
theorem old_ancestor
    (hS : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (s : ℝ) (hs : D.i₀ ≤ D.depth s) (i : Fin (p.activeCount D.Hm (D.depth s))) :
    forestAncestor p.lev p.par (D.old s i) D.i₀ = D.parent := by
  obtain ⟨hw, z, hzS, hzF⟩ := D.old_world s i
  have hlev : p.lev D.parent ≤ p.lev (D.old s i) := by
    rw [D.old_level s i]; exact hs
  have hz := hS hzS
  apply hp.ancestor_eq_of_interior hlev hw hzF hz.1
  have h2 : D.t₀ + D.q₀ = ((p.bin D.parent : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev D.parent) := by
    simp only [t₀, q₀, i₀]; field_simp
  rw [← h2]; exact hz.2

theorem old_assigned_subset
    (hS : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (s : ℝ) (hs : D.i₀ ≤ D.depth s) (i : Fin (p.activeCount D.Hm (D.depth s))) :
    p.assigned (D.old s i) ⊆ p.assigned D.parent := by
  have hlev : D.i₀ ≤ p.lev (D.old s i) := by rw [D.old_level s i]; exact hs
  have h := hp.ancestor_assignment_subset (D.old s i) D.i₀ hlev
  rwa [D.old_ancestor hp hS s hs i] at h

theorem old_block_subset
    (hS : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (s : ℝ) (hs : D.i₀ ≤ D.depth s) (i : Fin (p.activeCount D.Hm (D.depth s))) :
    Icc ((p.bin (D.old s i) : ℝ) / (2 : ℝ) ^ p.T (D.depth s))
        (((p.bin (D.old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (D.depth s)) ⊆
      Icc ((p.bin D.parent : ℝ) / (2 : ℝ) ^ p.T D.i₀)
        (((p.bin D.parent : ℝ) + 1) / (2 : ℝ) ^ p.T D.i₀) := by
  have hlev : D.i₀ ≤ p.lev (D.old s i) := by rw [D.old_level s i]; exact hs
  have h := hp.ancestor_time_subset (D.old s i) D.i₀ hlev
  rw [D.old_ancestor hp hS s hs i, D.old_level s i] at h
  exact h

/-- The relative dyadic block of a model label is its old block in parent time. -/
theorem old_relBin_mem
    (hS : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (s : ℝ) (hs : D.i₀ ≤ D.depth s) (i : Fin (p.activeCount D.Hm (D.depth s))) (t : ℝ) :
    t ∈ Icc ((p.bin (D.old s i) : ℝ) / (2 : ℝ) ^ p.T (p.lev (D.old s i)))
        (((p.bin (D.old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (D.old s i))) ↔
      (t - D.t₀) / D.q₀ ∈ IS (D.relT s) (D.relBin s i) := by
  have hsub := D.old_block_subset hp hS s hs i
  have hne : ((p.bin (D.old s i) : ℝ) / (2 : ℝ) ^ p.T (D.depth s)) ≤
      (((p.bin (D.old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (D.depth s)) := by
    apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hlo := (hsub ⟨le_rfl, hne⟩).1
  have hhi := (hsub ⟨hne, le_rfl⟩).2
  have hT : p.T D.i₀ ≤ p.T (D.depth s) := by
    by_contra hlt
    push Not at hlt
    have hA : (0 : ℝ) < (2 : ℝ) ^ p.T (D.depth s) := by positivity
    have hB : (0 : ℝ) < (2 : ℝ) ^ p.T D.i₀ := by positivity
    have hpow : (2 : ℝ) ^ p.T (D.depth s) < (2 : ℝ) ^ p.T D.i₀ :=
      pow_lt_pow_right₀ (by norm_num) hlt
    have hlen : ((p.bin (D.old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (D.depth s) -
        (p.bin (D.old s i) : ℝ) / (2 : ℝ) ^ p.T (D.depth s) ≤
        ((p.bin D.parent : ℝ) + 1) / (2 : ℝ) ^ p.T D.i₀ -
          (p.bin D.parent : ℝ) / (2 : ℝ) ^ p.T D.i₀ := by linarith
    rw [← sub_div, ← sub_div, add_sub_cancel_left, add_sub_cancel_left,
      div_le_div_iff₀ hA hB] at hlen
    linarith
  rw [D.old_level s i]
  exact relative_block_mem hT hlo hhi t

/-- The old bin of a model label lies in the parent block's range of sub-bins. -/
theorem old_bin_div
    (hS : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (s : ℝ) (hs : D.i₀ ≤ D.depth s) (i : Fin (p.activeCount D.Hm (D.depth s))) :
    p.T D.i₀ ≤ p.T (D.depth s) ∧ p.bin (D.old s i) / 2 ^ D.relT s = p.bin D.parent := by
  have hsub := D.old_block_subset hp hS s hs i
  have hne : ((p.bin (D.old s i) : ℝ) / (2 : ℝ) ^ p.T (D.depth s)) ≤
      (((p.bin (D.old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (D.depth s)) := by
    apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hlo := (hsub ⟨le_rfl, hne⟩).1
  have hhi := (hsub ⟨hne, le_rfl⟩).2
  have hT : p.T D.i₀ ≤ p.T (D.depth s) := by
    by_contra hlt
    push Not at hlt
    have hA : (0 : ℝ) < (2 : ℝ) ^ p.T (D.depth s) := by positivity
    have hB : (0 : ℝ) < (2 : ℝ) ^ p.T D.i₀ := by positivity
    have hpow : (2 : ℝ) ^ p.T (D.depth s) < (2 : ℝ) ^ p.T D.i₀ :=
      pow_lt_pow_right₀ (by norm_num) hlt
    have hlen : ((p.bin (D.old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (D.depth s) -
        (p.bin (D.old s i) : ℝ) / (2 : ℝ) ^ p.T (D.depth s) ≤
        ((p.bin D.parent : ℝ) + 1) / (2 : ℝ) ^ p.T D.i₀ -
          (p.bin D.parent : ℝ) / (2 : ℝ) ^ p.T D.i₀ := by linarith
    rw [← sub_div, ← sub_div, add_sub_cancel_left, add_sub_cancel_left,
      div_le_div_iff₀ hA hB] at hlen
    linarith
  exact ⟨hT, relative_block_div hT hlo hhi⟩

/-- Model labels of one depth with equal relative blocks have equal old bins. -/
theorem old_bin_eq_of_relBin
    (hS : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (s : ℝ) (hs : D.i₀ ≤ D.depth s) (i i' : Fin (p.activeCount D.Hm (D.depth s)))
    (h : D.relBin s i = D.relBin s i') : p.bin (D.old s i) = p.bin (D.old s i') := by
  have h1 := (D.old_bin_div hp hS s hs i).2
  have h2 := (D.old_bin_div hp hS s hs i').2
  have hm : p.bin (D.old s i) % 2 ^ D.relT s = p.bin (D.old s i') % 2 ^ D.relT s :=
    congrArg Fin.val h
  rw [← Nat.div_add_mod (p.bin (D.old s i)) (2 ^ D.relT s),
    ← Nat.div_add_mod (p.bin (D.old s i')) (2 ^ D.relT s), h1, h2, hm]

end Descendants

end SourceData

end

end Submission.Obl.k4_finite_affine_parent_sources
