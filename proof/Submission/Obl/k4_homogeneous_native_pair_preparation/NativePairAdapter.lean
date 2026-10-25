import Submission.Obl.k4_homogeneous_native_pair_preparation.Assembly
import Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux.KernelNativePairs

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open MeasureTheory Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split (I)

namespace ClassSample

variable {N : ℝ} {W : ℕ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
  {B : Fin W → ℝ} {f : ℝ → ℝ} {L h : ℝ} {M D : ℕ} {τ e : ℝ}
  (cs : ClassSample N W ω ν E B f L h M D τ e)

theorem trimmed_coarse_time (b : Fin cs.C) {p : (ℕ × (Fin 6 → ℝ)) × ℝ}
    (hp : p ∈ cs.trimmedIncidences b) :
    p.2 ∈ Ico (((nativeCoarseIndex (cs.j b) : ℕ) : ℝ) / (2 : ℝ) ^ cs.T)
      ((((nativeCoarseIndex (cs.j b) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ cs.T) := by
  have hs := cs.trimmed_selection b hp
  have h0 := fine_interval_subset_coarse (cs.j b) (Ico_subset_Icc_self hs.2.2.1)
  rw [nativeCoarseInterval_eq] at h0
  have hr : ((((cs.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (cs.T + cs.s)) ∈ I (cs.T + cs.s) (cs.j b) := by
    constructor
    · exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    · exact le_rfl
  have h1 := fine_interval_subset_coarse (cs.j b) hr
  rw [nativeCoarseInterval_eq] at h1
  exact ⟨h0.1, hs.2.2.1.2.trans_le h1.2⟩

noncomputable def pairData
    (Good : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (a : ℝ) : PairAux.Data where
  W := W
  T := cs.T
  s := cs.s
  C := cs.C
  γ := cs.γ
  j := cs.j
  R := cs.R
  A := cs.A
  F := cs.F
  B := B
  Good := Good
  κ₀ := cs.κ
  dfl := N ^ (-a)

theorem pairData_hyp
    (Good : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (a : ℝ)
    (hB : ∀ γ, 0 < B γ) (hGood : ∀ γ, MeasurableSet (Good γ)) :
    (cs.pairData Good a).Hyp E where
  κ₀one := cs.κ_one
  Bpos := hB
  Rdeg b := (cs.hchart b).2.2.2.2.1
  sel := by
    intro b p hp
    exact (cs.hchart b).2.2.2.2.2.2.2.2.2.2.1 p hp
  Sb_meas := cs.trimmed_measurable
  Sb_disjoint := by
    intro b b' hne hγ
    exact cs.trimmed_disjoint hne hγ
  Sb_coarse := cs.trimmed_coarse_time
  Good_meas := hGood

end ClassSample

/-- The explicit finite-index construction, using the native specialization
of the parent tree's checked pair-mask argument. -/
theorem sample_preparation : SamplePreparation := by
  intro M D
  refine ⟨3 * M + 4, max D 1, ?_⟩
  intro N K W ω ν E P B f g G L S h e u a c τ ε depths Good cs
    hN he hτε hω hωsum hν hB hEm hEt hK1 hKpow hncls hslack hgeom hgood hder hfloor hGood hbad
  letI : ∀ γ, IsProbabilityMeasure (ν γ) := hν
  have hN1 : 1 ≤ N := one_le_two.trans hN
  have hN0 : 0 < N := zero_lt_one.trans_le hN1
  have hn1 : 1 ≤ (cs.ncls : ℝ) := by exact_mod_cast cs.ncls_one
  obtain ⟨hκ1, hκold, hKκ, hκpow, hm, hfloor', hgeom', hbudget, hκmass⟩ :=
    preparation_numeric_bounds hN1 cs.κ_one hn1 hK1 cs.κ_le hncls hKpow
      hslack hgeom hgood hder hfloor
  let q := cs.pairData Good a
  letI : ∀ w : Fin q.W, IsProbabilityMeasure (ν w) := fun w => hν w
  have hq : q.Hyp E := cs.pairData_hyp Good a hB (fun γ => (hGood γ).1)
  have hbad' : (∑ γ, ENNReal.ofReal (ω γ) * ((ν γ).prod volume) (E γ \ Good γ)) ≤
      ENNReal.ofReal (N ^ (-c)) := by
    convert hbad using 1
    apply Finset.sum_congr rfl
    intro γ _
    have heq : E γ \ Good γ = (Good γ)ᶜ ∩ E γ := by
      ext p
      simp only [mem_sdiff, mem_inter_iff, mem_compl_iff, and_comm]
    rw [Measure.restrict_apply (hGood γ).1.compl, heq]
  have hcov := hq.native_coverage_of_budgets ν ω hω hωsum hEm hEt
    hm (Real.rpow_nonneg hN0.le (-c))
    (zero_lt_one.trans_le hκ1) (Real.rpow_nonneg hN0.le (-a)) hfloor'
    cs.retained_mass_le hbad' (by
      convert hbudget using 1 <;> dsimp [q, ClassSample.pairData] <;> ring)
    hκmass
  apply cs.native_of_pairs P g G S a u K (preparedSlack cs.κ cs.ncls K) ε depths Good
    q.nativePairs hN hτε (zero_lt_one.trans_le hK1) hκ1 hκpow hκold hKκ hB
    (hgeom' ((2 : ℝ) ^ cs.s) (by positivity) cs.hs₂) hGood ?_ hcov
  intro b b'
  refine ⟨hq.nativePairs_meas b b', ?_⟩
  intro p hp
  obtain ⟨hγ, hj, hF, hF', hG, hG', h00, h01, h10, h11⟩ := hp
  have hj' : (cs.j b : ℕ) / 2 ^ cs.s = (cs.j b' : ℕ) / 2 ^ cs.s := by
    change nativeCoarseIndex (cs.j b) = nativeCoarseIndex (cs.j b') at hj
    simpa only [nativeCoarseIndex_val] using congrArg Fin.val hj
  refine ⟨hγ, hj', hF, hF', hG, hG', ?_⟩
  intro R' hR' t ht
  rcases hR' with rfl | rfl <;> rcases ht with rfl | rfl
  · simpa only [q, ClassSample.pairData, mul_comm] using h00
  · simpa only [q, ClassSample.pairData, mul_comm] using h01
  · simpa only [q, ClassSample.pairData, mul_comm] using h10
  · simpa only [q, ClassSample.pairData, mul_comm] using h11

end Submission.Obl.k4_homogeneous_native_pair_preparation
