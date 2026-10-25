-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeMergedPrediction, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeMergedPrediction.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeMergedPrediction.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeMergedPrediction.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeMergedPrediction.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativePredictionAssembly
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMergedMultiplicity
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripPath

/-! Concrete terminal lists and finite-format success sets for the two-scale
merged strip atlas. Their bounds depend on the OLD packet lists and a fixed
250 neighboring parameter bins, independently of the heavy net size. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped BigOperators

namespace NativeMergedPrediction

variable {W : ℕ} {p : PathData W} {i : ℕ}
    (d : StripRefinement (p.StripLevel i))
    (rawNormal : p.StripLevel i → Fin p.C → StripSpace)
    (rawOffset : p.StripLevel i → Fin p.C → ℝ)

open Classical in
def rawCodeList (b : p.StripLevel i) (f : Fin p.C) :
    Finset (StripCodeLabel d.radius (d.normal b) (d.offset b)) :=
  (stripParameterList d.radius (rawNormal b f) (rawOffset b f) 2).subtype
    (fun q => q ∈ stripParameterCodes d.radius (d.normal b) (d.offset b))

theorem rawCodeList_card (b : p.StripLevel i) (f : Fin p.C) :
    (rawCodeList d rawNormal rawOffset b f).card ≤ 250 := by
  classical
  calc
    _ ≤ (stripParameterList d.radius (rawNormal b f) (rawOffset b f) 2).card := by
      rw [rawCodeList, Finset.card_subtype]
      exact Finset.card_filter_le _ _
    _ ≤ 250 := by simpa using stripParameterList_card_le d.radius (rawNormal b f) (rawOffset b f) 2

open Classical in
def parameterList (m : ℕ) (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    Finset d.MergedParameterLabel :=
  ((terminalAncestorList p m w o).subtype (fun b => p.lev b = i)).biUnion (fun b =>
    (terminalAncestorList p m w o).biUnion (fun f =>
      (rawCodeList d rawNormal rawOffset b f).image
        (fun q => (⟨b, q⟩ : d.MergedParameterLabel))))

def success (m stop : ℕ) (b : p.StripLevel i) (code : StripParameterCode) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  packetPredictionUnion (p.packetWitness m stop (p.γ b.val))
    (fun f => code ∈ stripParameterList d.radius (rawNormal b f) (rawOffset b f) 2)

section Path

variable {N L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem parameterList_card
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    ((parameterList d rawNormal rawOffset m w o).card : ℝ) ≤ 250 * (m * p.κ) ^ 2 := by
  classical
  let old := terminalAncestorList p m w o
  have hinner (b : p.StripLevel i) :
      (old.biUnion (fun f => (rawCodeList d rawNormal rawOffset b f).image
        (fun q => (⟨b, q⟩ : d.MergedParameterLabel)))).card ≤ old.card * 250 := by
    calc
      _ ≤ ∑ f ∈ old, ((rawCodeList d rawNormal rawOffset b f).image
          (fun q => (⟨b, q⟩ : d.MergedParameterLabel))).card := Finset.card_biUnion_le
      _ ≤ ∑ _f ∈ old, 250 := Finset.sum_le_sum (fun f _ =>
        Finset.card_image_le.trans (rawCodeList_card d rawNormal rawOffset b f))
      _ = _ := by simp
  have hNat : (parameterList d rawNormal rawOffset m w o).card ≤ old.card ^ 2 * 250 := by
    calc
      _ ≤ ∑ b ∈ old.subtype (fun b => p.lev b = i),
          (old.biUnion (fun f => (rawCodeList d rawNormal rawOffset b f).image
            (fun q => (⟨b, q⟩ : d.MergedParameterLabel)))).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ old.subtype (fun b => p.lev b = i), old.card * 250 :=
        Finset.sum_le_sum (fun b _ => hinner b)
      _ = (old.subtype (fun b => p.lev b = i)).card * (old.card * 250) := by simp
      _ ≤ old.card * (old.card * 250) := by
        apply Nat.mul_le_mul_right
        rw [Finset.card_subtype]
        exact Finset.card_filter_le _ _
      _ = _ := by ring
  have hκ : 0 ≤ p.κ := le_trans (by norm_num) hp.1
  have hbound : (old.card : ℝ) ≤ m * p.κ := terminalAncestorList_card p m hp.2.2.2.2.2.1 w o
  calc
    _ ≤ (old.card : ℝ) ^ 2 * 250 := by exact_mod_cast hNat
    _ ≤ 250 * (m * p.κ) ^ 2 := by nlinarith [sq_nonneg ((m : ℝ) * p.κ - old.card)]

theorem measurableSet_success
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (stop : ℕ) (b : p.StripLevel i) (code : StripParameterCode) :
    MeasurableSet (success d rawNormal rawOffset m stop b code) :=
  measurableSet_packetPredictionUnion _ (hp.measurableSet_packetWitness stop (p.γ b.val)) _

theorem success_section_format
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 0 < N)
    (stop : ℕ) (b : p.StripLevel i) (code : StripParameterCode) (copy : ℕ) :
    gfmt 7 ((p.C : ℝ) * (N ^ Mp + 2 * (p.C : ℝ) ^ 2 * N ^ Mp + (p.C : ℝ) * N ^ Mp)) Dp
      {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈
        success d rawNormal rawOffset m stop b code} :=
  packetPredictionUnion_format (by positivity) _
    (fun f => hp.packetWitness_section_format hN stop (p.γ b.val) f copy) _

theorem success_format_polynomial_budget
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 2 ≤ N) :
    (p.C : ℝ) * (N ^ Mp + 2 * (p.C : ℝ) ^ 2 * N ^ Mp + (p.C : ℝ) * N ^ Mp) ≤
      N ^ (4 * Mp + 2) := by
  let H := N ^ Mp
  have hN1 : 1 ≤ N := by linarith
  have hH : 1 ≤ H := one_le_pow₀ hN1
  have hc : (p.C : ℝ) ≤ H := hp.2.2.1
  have h1 : (p.C : ℝ) * H ≤ H ^ 4 := by
    calc
      _ ≤ H ^ 2 := by nlinarith
      _ ≤ _ := pow_le_pow_right₀ hH (by norm_num)
  have h2 : (p.C : ℝ) ^ 3 * H ≤ H ^ 4 := by
    calc
      _ ≤ H ^ 3 * H := by gcongr
      _ = _ := by ring
  have h3 : (p.C : ℝ) ^ 2 * H ≤ H ^ 4 := by
    calc
      _ ≤ H ^ 3 := by nlinarith [mul_nonneg (show 0 ≤ H - p.C by linarith) (sq_nonneg H)]
      _ ≤ _ := pow_le_pow_right₀ hH (by norm_num)
  calc
    _ = (p.C : ℝ) * H + 2 * (p.C : ℝ) ^ 3 * H + (p.C : ℝ) ^ 2 * H := by dsimp only [H]; ring
    _ ≤ 4 * H ^ 4 := by linarith
    _ = 4 * N ^ (4 * Mp) := by dsimp only [H]; rw [← pow_mul, Nat.mul_comm Mp 4]
    _ ≤ _ := by
      rw [pow_add]
      have hh : 4 ≤ N ^ 2 := by nlinarith
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ N ^ (4 * Mp))

theorem success_section_format_power
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 2 ≤ N)
    (stop : ℕ) (b : p.StripLevel i) (code : StripParameterCode) (copy : ℕ) :
    gfmt 7 (N ^ (4 * Mp + 2)) Dp
      {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈
        success d rawNormal rawOffset m stop b code} :=
  Submission.Lib.K4RepresentativeAssembly.fmt_mono
    (success_section_format d rawNormal rawOffset hp (by linarith) stop b code copy)
    (success_format_polynomial_budget hp hN) le_rfl

/-- This is exactly the `hknown` parameter-list input of the merged backend. -/
theorem merged_parameter_known
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (stop : ℕ) (width aL : ℝ) (haL : aL = δ N L)
    (a : d.MergedLabel) (x : (ℕ × (Fin 6 → ℝ)) × ℝ)
    (hx : x ∈ d.mergedIncidence (p.stripParent i) width
      (success d rawNormal rawOffset m stop) a) :
    d.mergedParameterLabel a ∈ parameterList d rawNormal rawOffset m
      (p.stripParent i a.1).world (gobs (B (p.stripParent i a.1).world) aL x) := by
  classical
  let w := p.γ a.1.val
  have hcoarse : x ∈ p.F a.1.val := hx.1.1
  obtain ⟨f, hfcode, hfwit⟩ := hx.2
  have hfList := hp.packetWitness_known stop w f hfwit
  have hclean : packetUnique p.lev p.γ p.F w x ∧ x ∈ p.terminalCoverage m w := by
    by_cases hf : p.lev f = stop ∧ p.γ f = w <;> dsimp only [w] at hf
    · have hh : x ∈ (p.F f ∩ {z | packetUnique p.lev p.γ p.F w z}) ∩ p.terminalCoverage m w := by
        simpa only [PathData.packetWitness, ite_eq_left hf] using hfwit
      exact ⟨hh.1.2, hh.2⟩
    · simp only [PathData.packetWitness, ite_eq_right hf, mem_empty_iff_false] at hfwit
  obtain ⟨t, ht, hxt⟩ := hclean.2
  have hbList := hp.terminalAncestorList_mem w x hclean.1 ⟨t, ht.1, ht.2, hxt⟩ a.1.val rfl hcoarse
  subst aL
  change d.mergedParameterLabel a ∈ parameterList d rawNormal rawOffset m w (obs (B w) (δ N L) x)
  apply Finset.mem_biUnion.mpr
  refine ⟨a.1, ?_, ?_⟩
  · simpa only [Finset.mem_subtype] using hbList
  · apply Finset.mem_biUnion.mpr
    refine ⟨f, hfList, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨a.2.1, by simpa only [rawCodeList, Finset.mem_subtype] using hfcode, rfl⟩

end Path

end NativeMergedPrediction

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
