-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/SamplePruning.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.SampleRawFacts
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.PathBudgets
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.FinitePacketSums

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
open MeasureTheory MvPolynomial Set Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets
section
variable {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
  {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
  {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ} {κ : ℝ} {C : ℕ}
  {lev : Fin C → ℕ} {par : Fin C → Fin C} {γ : Fin C → Fin W} {j : Fin C → ℕ}
  {c u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
  {R : Fin C → MvPolynomial (Fin 4) ℝ} {A : Fin C → Set (ℕ × (Fin 6 → ℝ))}
  {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
  {lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)}

variable {Mpr Dpr Mg Dg : ℕ} {d₁ ρ gain τ ε : ℝ} {n : ℕ} {old : Fin n → Fin C}
  {R' : Fin n → MvPolynomial (Fin 4) ℝ} {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))}
  {V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {q : ℝ} {i : ℕ} {h : ℝ} {s₀ K : ℕ}


/-- Packet-relative light pruning of the actual witnesses, using the unchanged
old priors. Every retained entry has positive world weight. -/
theorem sampleInput_pruned_entries (hNk : 1 ≤ Nk)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (hK : κ * (2 : ℝ) ^ s₀ ≤ K)
    (hlight : 4 * Nk ^ (-ε - τ) ≤ Nk ^ (-ε) / 64) :
    let exponent := (d₁ * h + 4 * ρ * gain) * L + 4 * ε
    let geom := (2 : ℝ) ^ s₀ * (2 * (K : ℝ) + 2) ^ 2 * 4
    ∃ cov : Entry n s₀ K → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ e, MeasurableSet (cov e)) ∧
      (∀ e, ∀ p ∈ cov e, p ∈ V e.1 ∧ p.1 ∈ memE old R' A' j c u Q R (T i) s₀ K e ∧
        p.2 ∈ subBlock (T i) s₀ (j (old e.1)) e.2.1) ∧
      (∀ e e', e ≠ e' → γ (old e.1) = γ (old e'.1) → Disjoint (cov e) (cov e')) ∧
      (∀ e, (cov e).Nonempty → 0 < ω (γ (old e.1)) ∧
        (ENNReal.ofReal (((2 : ℝ) ^ T i)⁻¹) * ν (γ (old e.1)) (A (old e.1))) *
          ENNReal.ofReal (Nk ^ (-exponent - ε - τ) / geom) ≤
            ((ν (γ (old e.1))).prod volume) (cov e)) ∧
      ENNReal.ofReal (Nk ^ (-ε) / 4) ≤
        ∑ e, ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (cov e) := by
  classical
  let exponent := (d₁ * h + 4 * ρ * gain) * L + 4 * ε
  let geom := (2 : ℝ) ^ s₀ * (2 * (K : ℝ) + 2) ^ 2 * 4
  let raw := rawCov old R' A' j c u Q R (T i) s₀ K V
  let packet : Entry n s₀ K → {b : Fin C // lev b = i} := fun e =>
    ⟨old e.1, (hsi.2.2.2.2.2.2.2.1 e.1).1⟩
  let mass := fun e : Entry n s₀ K => ((ν (γ (old e.1))).prod volume) (raw e)
  let scale := fun b : {b : Fin C // lev b = i} =>
    ENNReal.ofReal (((2 : ℝ) ^ T i)⁻¹) * ν (γ b.val) (A b.val)
  let rwgt := fun b : {b : Fin C // lev b = i} => ω (γ b.val)
  let weight := fun b : {b : Fin C // lev b = i} => ENNReal.ofReal (rwgt b)
  let count := ENNReal.ofReal (Nk ^ exponent * geom)
  let threshold := ENNReal.ofReal (Nk ^ (-exponent - ε - τ) / geom)
  obtain ⟨hrawm, hrawsub, hrawdisj, hrawsum⟩ := sampleInput_rawCover_facts hsi hpath hK
  have hNpos : 0 < Nk := zero_lt_one.trans_le hNk
  have hgeom : 0 < geom := by dsimp [geom]; positivity
  have hcount : ∀ b, ((Finset.univ.filter (fun e => packet e = b)).card : ENNReal) ≤ count := by
    intro b
    have hfilter : Finset.univ.filter (fun e : Entry n s₀ K => packet e = b) =
        Finset.univ.filter (fun e : Entry n s₀ K => old e.1 = b.val) := by
      ext e
      simp [packet, Subtype.ext_iff]
    rw [hfilter]
    have hh := card_Entry_packet_le (s₀ := s₀) (K := K) old b.val (hsi.2.2.2.2.2.2.2.2.2.1 b.val)
    have hh' : ((Finset.univ.filter (fun e : Entry n s₀ K => old e.1 = b.val)).card : ℝ) ≤
        Nk ^ exponent * geom := by
      simpa only [exponent, geom, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hh
    simpa only [ENNReal.ofReal_natCast, count] using ENNReal.ofReal_le_ofReal hh'
  have hbudget : (∑ b, weight b * scale b) ≤ 1 := path_level_prior_budget hsi.1 hpath i
  have hmass : ENNReal.ofReal (Nk ^ (-ε) / 2) ≤ ∑ e, weight (packet e) * mass e := by
    change ENNReal.ofReal (Nk ^ (-ε) / 2) ≤
      ∑ e, ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (raw e)
    rw [hrawsum]
    exact hsi.2.2.2.2.2.2.2.2.2.2.2.1
  have hcost_eq : count * threshold = ENNReal.ofReal (Nk ^ (-ε - τ)) := by
    dsimp only [count, threshold]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    calc
      _ = Nk ^ exponent * Nk ^ (-exponent - ε - τ) := by field_simp [hgeom.ne'] <;> ring
      _ = _ := by rw [← Real.rpow_add hNpos]; congr 1 <;> ring
  have hcost : count * threshold ≤ ENNReal.ofReal ((Nk ^ (-ε) / 2) / 2) := by
    rw [hcost_eq]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [Real.rpow_nonneg hNpos.le (-ε)]
  have hret := heavy_entries_retain_half packet mass scale weight count threshold hcount hbudget
    (by positivity : 0 ≤ Nk ^ (-ε) / 2) hmass hcost
  have hpos := positive_heavy_sum_eq packet mass scale rwgt threshold (fun b => hsi.1.2.1 _)
  rw [hpos] at hret
  let keep := fun e : Entry n s₀ K => 0 < rwgt (packet e) ∧ scale (packet e) * threshold ≤ mass e
  let cov := fun e : Entry n s₀ K => if keep e then raw e else ∅
  have hsub (e) : cov e ⊆ raw e := by
    intro p hp
    by_cases he : keep e
    · simpa only [cov, if_pos he] using hp
    · simp only [cov, if_neg he, Set.mem_empty_iff_false] at hp
  dsimp only
  refine ⟨cov, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    by_cases he : keep e
    · simpa only [cov, if_pos he] using hrawm e
    · simp only [cov, if_neg he, MeasurableSet.empty]
  · intro e p hp
    exact hrawsub e p (hsub e hp)
  · intro e e' hne hworld
    exact (hrawdisj e e' hne hworld).mono (hsub e) (hsub e')
  · intro e hne
    by_cases he : keep e
    · exact ⟨he.1, by simpa only [cov, if_pos he] using he.2⟩
    · have : cov e = ∅ := by simp only [cov, if_neg he]
      exact False.elim (Set.not_nonempty_empty (this ▸ hne))
  · have heq : (∑ e, ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (cov e)) =
        ∑ e ∈ Finset.univ.filter keep, weight (packet e) * mass e := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : keep e
      · simp only [cov, he, ite_true]
        rfl
      · simp only [cov, he, ite_false, measure_empty, mul_zero]
    rw [heq]
    convert hret using 1 <;> congr 1 <;> ring

end
end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
