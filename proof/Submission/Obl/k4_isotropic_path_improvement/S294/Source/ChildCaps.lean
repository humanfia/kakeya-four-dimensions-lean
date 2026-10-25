-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.ChildCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The cap clauses of the relative row packet at a child (session x1088).

For a child `b` below an ancestor `a` (same world, `F_b ⊆ F_a`) and ANY measurable event set
`Se ⊆ F_b ∩ base`, the base ceiling (`OriginalPacketCaps.base_cap`, the old packet `b`) and the
band cap of the ancestor signal in child units, `R_a / δ(N, r_b)` (x1095's
`ancestor_child_band_mass_cap`, root `a`, child `b`), are the first two clauses of `CapClauses`
with the child's full reference `2^-T_b ν(A_b)`, once their constants are below `K` and the band
widths are resolved (`N^-(L - r_b) ≤ 4 ε`). `childCapClauses` adds a census in clause form. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Clauses
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalPacketCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorClockBandMass
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.UniformBoundsPreparation
import Submission.Lib.K4ParentSignalPreparation.Census

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open MeasureTheory Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
open scoped ENNReal

noncomputable section

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ ε₀ : ℝ}

/-- **Base ceiling and band cap at a child**, in the literal `CapClauses` form. -/
theorem child_base_band_caps (Q : PreparedAngularPath d k p m H u τ)
    (hpure : Q.uniformPureBounds ε₀) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (a b : Fin p.C) (hγ : p.γ a = p.γ b) (hFab : p.F b ⊆ p.F a)
    (hscale : O204.Split.δ (d.N k) (p.r (p.lev b)) ≤ O204.Split.δ (d.N k) (p.r (p.lev a)))
    (hr0 : 0 ≤ p.r (p.lev b)) (hrL : p.r (p.lev b) ≤ d.L) (hA0 : d.ν k (p.γ b) (p.A b) ≠ 0)
    {d₁ : ℝ} (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1)
    (hprof : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - d.f 0 - d₁ * r| ≤ δ₀ * d.L)
    {K ε : ℝ} (hε : 0 < ε) (hres : d.N k ^ (-(d.L - p.r (p.lev b))) ≤ 4 * ε)
    (hKbase : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * d.N k ^ (τ + 2 * δ₀ * d.L + ε₀) ≤ K)
    (hKband : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ d₁ *
      d.N k ^ (2 * (δ₀ * d.L) + (τ + 2 * δ₀ * d.L) + ε₀) ≤ K)
    (Se : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hSem : MeasurableSet Se)
    (hSeF : Se ⊆ p.F b) (hSebase : Se ⊆ Q.base (p.γ b)) :
    (∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet U →
      (((d.ν k (p.γ b)).prod volume).restrict Se)
          {z | O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b) z ∈ U} ≤
        ENNReal.ofReal K * (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) *
          volume U) ∧
    (∀ w : ℝ, ε ≤ w → w ≤ 1 → ∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet U → ∀ f : EuclideanSpace ℝ (Fin 3) → ℝ, Measurable f →
      (((d.ν k (p.γ b)).prod volume).restrict Se)
          {z | O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b) z ∈ U ∧
            |O204.Tangent.packetSignal (p.R a) z / O204.Split.δ (d.N k) (p.r (p.lev b)) -
              f (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b) z)| ≤ w} ≤
        ENNReal.ofReal (K * w ^ d₁) *
          (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) * volume U) := by
  have hceil := hpure.ceiling
  -- `Se` lies in the problem's event set
  have hSeE : Se ⊆ d.E k (p.γ b) := by
    intro z hz
    obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 b
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hF, -⟩ := hch
    exact (hF z (hSeF hz)).1
  refine ⟨fun U hU => ?_, fun w hw hw1 U hU f hf => ?_⟩
  · have h := OriginalPacketCaps.base_cap Q hceil hd hp b hr0 hrL Se hSem hSeE hSebase hSeF hA0 U hU
    refine le_trans h ?_
    gcongr
  · -- the band cap of the ancestor signal in child units
    have hw0 : 0 < w := lt_of_lt_of_le hε hw
    have hμ : ((d.ν k (p.γ b)).prod volume).restrict Se ≤ d.μ k (p.γ a) := by
      rw [hγ]
      exact Measure.restrict_mono hSeE le_rfl
    have hae : ∀ P : ((ℕ × (Fin 6 → ℝ)) × ℝ) → Prop, (∀ z ∈ Se, P z) →
        ∀ᵐ z ∂(((d.ν k (p.γ b)).prod volume).restrict Se), P z :=
      fun P hP => (ae_restrict_mem hSem).mono hP
    have h := Q.ancestor_child_band_mass_cap hceil hd hp a b hγ.symm hscale
      hr0 hrL (((d.ν k (p.γ b)).prod volume).restrict Se) hμ
      (hae _ (fun z hz => by rw [hγ]; exact hSebase hz)) (hae _ (fun z hz => hFab (hSeF hz)))
      (hae _ (fun z hz => hSeF hz)) hd₀ hprof f hf hw0 (hres.trans (by linarith)) U hU
    have hsig : ∀ z, O204.Tangent.packetSignal (p.R a) z / O204.Split.δ (d.N k) (p.r (p.lev b)) =
        physicalParentSignal (d.N k) p b (p.R a) z := by
      intro z
      change _ = (O204.Split.δ (d.N k) (p.r (p.lev b)))⁻¹ * _
      rw [div_eq_inv_mul]
      rfl
    have hset : {z : (ℕ × (Fin 6 → ℝ)) × ℝ |
        O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b) z ∈ U ∧
          |O204.Tangent.packetSignal (p.R a) z / O204.Split.δ (d.N k) (p.r (p.lev b)) -
            f (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b) z)| ≤ w} =
        {z | unshearedPacketBase p b z ∈ U ∧
          |physicalParentSignal (d.N k) p b (p.R a) z - f (unshearedPacketBase p b z)| ≤ w} := by
      ext z
      have h := hsig z
      show (_ ∧ _) ↔ (_ ∧ _)
      rw [h]
      exact Iff.rfl
    rw [hset]
    refine le_trans h ?_
    rw [mul_comm (d.ν k (p.γ b) (p.A b))]
    gcongr

/-- **The census conjunct** of `CapClauses` from an occupied-code census (the form of x1095's
`exists_multiscale_ancestor_census_source`) with constant `Kc ≤ K`, at all meshes down to a
fine mesh `≤ ε`, under the census shape `Kc^100 base ≤ (a'/h') hidden`. -/
theorem census_clause_of_occupied {K Kc ε d₁ h' a' fineMesh : ℝ}
    (Se : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (zb : ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 3))
    (Xnb : ((ℕ × (Fin 6 → ℝ)) × ℝ) → ℝ) (hε : 0 < ε) (hh' : 0 < h') (hKc1 : 1 ≤ Kc)
    (hKc : Kc ≤ K) (hfine : fineMesh ≤ ε)
    (hocc : ∀ base hidden : ℝ, fineMesh ≤ base → base ≤ 1 → fineMesh ≤ hidden → hidden ≤ 1 →
      Kc ^ (100 : ℕ) * base ≤ (a' / h') * hidden →
      (Submission.Lib.K4ParentSignalPreparation.Census.occupied Se (fun z j => zb z j) Xnb base
        hidden).Finite ∧
      ((Submission.Lib.K4ParentSignalPreparation.Census.occupied Se (fun z j => zb z j) Xnb base
        hidden).ncard : ℝ) ≤ Kc / (base ^ 3 * hidden ^ d₁)) :
    ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 → K ^ (100 : ℕ) * h' * p ≤ a' * w →
      Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se,
        (fun e => (fun i : Fin 3 => ⌊zb e i / p⌋, ⌊Xnb e / w⌋)) e = k} ∧
      (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se,
        (fun e => (fun i : Fin 3 => ⌊zb e i / p⌋, ⌊Xnb e / w⌋)) e = k}).ncard : ℝ) ≤
          K / (p ^ (3 : ℕ) * w ^ d₁) := by
  intro pm w hp hp1 hw hw1 hshape
  have hpm0 : 0 < pm := lt_of_lt_of_le hε hp
  have hw0 : 0 < w := lt_of_lt_of_le hε hw
  have hshape' : Kc ^ (100 : ℕ) * pm ≤ (a' / h') * w := by
    have hKpow : Kc ^ (100 : ℕ) ≤ K ^ (100 : ℕ) := pow_le_pow_left₀ (by linarith) hKc 100
    have h1 : K ^ (100 : ℕ) * pm ≤ (a' / h') * w := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hh']
      have : K ^ (100 : ℕ) * pm * h' = K ^ (100 : ℕ) * h' * pm := by ring
      linarith
    calc Kc ^ (100 : ℕ) * pm ≤ K ^ (100 : ℕ) * pm := by gcongr
      _ ≤ _ := h1
  obtain ⟨hfin, hcard⟩ := hocc pm w (hfine.trans hp) hp1 (hfine.trans hw) hw1 hshape'
  refine ⟨hfin, le_trans hcard ?_⟩
  exact div_le_div_of_nonneg_right hKc (by positivity)

/-- **The cap clauses at a child**: base ceiling and band cap (`child_base_band_caps`) and an
occupied-code census (`census_clause_of_occupied`), in the literal `CapClauses` form. -/
theorem childCapClauses (Q : PreparedAngularPath d k p m H u τ)
    (hpure : Q.uniformPureBounds ε₀) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (a b : Fin p.C) (hγ : p.γ a = p.γ b) (hFab : p.F b ⊆ p.F a)
    (hscale : O204.Split.δ (d.N k) (p.r (p.lev b)) ≤ O204.Split.δ (d.N k) (p.r (p.lev a)))
    (hr0 : 0 ≤ p.r (p.lev b)) (hrL : p.r (p.lev b) ≤ d.L) (hA0 : d.ν k (p.γ b) (p.A b) ≠ 0)
    {d₁ : ℝ} (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1)
    (hprof : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - d.f 0 - d₁ * r| ≤ δ₀ * d.L)
    {K ε h' a' Kc fineMesh : ℝ} (hε : 0 < ε) (hres : d.N k ^ (-(d.L - p.r (p.lev b))) ≤ 4 * ε)
    (hKbase : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * d.N k ^ (τ + 2 * δ₀ * d.L + ε₀) ≤ K)
    (hKband : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ d₁ *
      d.N k ^ (2 * (δ₀ * d.L) + (τ + 2 * δ₀ * d.L) + ε₀) ≤ K)
    (Se : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hSem : MeasurableSet Se)
    (hSeF : Se ⊆ p.F b) (hSebase : Se ⊆ Q.base (p.γ b))
    (hh' : 0 < h') (hKc1 : 1 ≤ Kc) (hKc : Kc ≤ K) (hfine : fineMesh ≤ ε)
    (hocc : ∀ base hidden : ℝ, fineMesh ≤ base → base ≤ 1 → fineMesh ≤ hidden → hidden ≤ 1 →
      Kc ^ (100 : ℕ) * base ≤ (a' / h') * hidden →
      (Submission.Lib.K4ParentSignalPreparation.Census.occupied Se
        (fun z j => O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b) z j)
        (fun z => O204.Tangent.packetSignal (p.R a) z / O204.Split.δ (d.N k) (p.r (p.lev b)))
        base hidden).Finite ∧
      ((Submission.Lib.K4ParentSignalPreparation.Census.occupied Se
        (fun z j => O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b) z j)
        (fun z => O204.Tangent.packetSignal (p.R a) z / O204.Split.δ (d.N k) (p.r (p.lev b)))
        base hidden).ncard : ℝ) ≤ Kc / (base ^ 3 * hidden ^ d₁)) :
    CapClauses K ε d₁ h' a'
      (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
      (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
      (fun z => O204.Tangent.packetSignal (p.R a) z / O204.Split.δ (d.N k) (p.r (p.lev b))) Se := by
  obtain ⟨hbase, hband⟩ := child_base_band_caps Q hpure hd hp a b hγ hFab hscale hr0 hrL hA0 hd₀
    hd₁ hprof hε hres hKbase hKband Se hSem hSeF hSebase
  exact ⟨hbase, hband, census_clause_of_occupied Se _ _ hε hh' hKc1 hKc hfine hocc⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
