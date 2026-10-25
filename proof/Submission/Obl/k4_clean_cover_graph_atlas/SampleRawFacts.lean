import Submission.Obl.k4_clean_cover_graph_atlas.SampleCover
import Submission.Obl.k4_clean_cover_graph_atlas.EntryIncidences

namespace Submission.Obl.k4_clean_cover_graph_atlas
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


/-- The half-open convention in the covered-entry and incidence APIs is identical. -/
theorem rawCov_eq_openEntryIncidences (e : Entry n s₀ K) :
    rawCov old R' A' j c u Q R (T i) s₀ K V e =
      openEntryIncidences old R' A' j c u Q R (T i) s₀ K V e := by
  ext p
  simp only [rawCov, openEntryIncidences, entryIncidences, subIco, subBlock,
    Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ico, Set.mem_Icc]
  constructor
  · rintro ⟨hpV, hpM, htlo, hthi⟩
    exact ⟨⟨hpV, hpM, htlo, hthi.le⟩, hthi⟩
  · rintro ⟨⟨hpV, hpM, htlo, _⟩, hthi⟩
    exact ⟨hpV, hpM, htlo, hthi⟩

/-- The actual sampled witnesses admit a measurable, disjoint entry refinement
with exactly the same original weighted mass. -/
theorem sampleInput_rawCover_facts
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (hK : κ * (2 : ℝ) ^ s₀ ≤ K) :
    let cov := rawCov old R' A' j c u Q R (T i) s₀ K V
    (∀ e, MeasurableSet (cov e)) ∧
    (∀ e, ∀ p ∈ cov e, p ∈ V e.1 ∧ p.1 ∈ memE old R' A' j c u Q R (T i) s₀ K e ∧
      p.2 ∈ subBlock (T i) s₀ (j (old e.1)) e.2.1) ∧
    (∀ e e', e ≠ e' → γ (old e.1) = γ (old e'.1) → Disjoint (cov e) (cov e')) ∧
    (∑ e, ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (cov e)) =
      ∑ a, ENNReal.ofReal (ω (γ (old a))) * ((ν (γ (old a))).prod volume) (V a) := by
  classical
  have hentry := hsi.2.2.2.2.2.2.2.1
  have hformat : ∀ a z, gfmt 6 (Nk ^ Mg) Dg {x | (z, x) ∈ A' a} := by
    intro a z
    obtain ⟨_, _, _, _, _, _, hf, _⟩ := hentry a
    exact hf z
  have hdeg : ∀ a, (R' a).totalDegree ≤ 2 := by
    intro a
    obtain ⟨_, _, hd, _⟩ := hentry a
    exact hd
  have hdegOld : ∀ b, (R b).totalDegree ≤ 2 := by
    intro b
    obtain ⟨_, _, _, _, hd, _⟩ := (hpath.2.2.2.2.2.2.2 b).2.2
    exact hd
  have hVm : ∀ a, MeasurableSet (V a) := by
    intro a
    obtain ⟨_, _, _, _, _, _, _, _, hm, _⟩ := hentry a
    exact hm
  have hV : ∀ a, ∀ p ∈ V a, p.1 ∈ A' a ∧
      p.2 ∈ Icc ((j (old a) : ℝ) / (2 : ℝ) ^ T i) (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ T i) := by
    intro a p hp
    obtain ⟨_, _, _, _, _, _, _, _, _, hsub, _⟩ := hentry a
    exact ⟨(hsub hp).2.1, (hsub hp).2.2.1⟩
  have hzc : ∀ a, ∀ l ∈ A' a, ∀ t ∈ Icc ((j (old a) : ℝ) / (2 : ℝ) ^ T i)
      (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ T i),
      ‖zc (Q (old a)) (c (old a)) (u (old a)) l t‖ ≤ κ := by
    intro a l hl t ht
    obtain ⟨hlev, _, _, _, _, hsub, _⟩ := hentry a
    have hc := (hpath.2.2.2.2.2.2.2 (old a)).2.2
    rw [hlev] at hc
    obtain ⟨_, _, _, _, _, _, _, _, _, hg, _⟩ := hc
    exact ((hg l (hsub hl)).2.2 t ht).1
  have hKside : κ ≤ (K : ℝ) * side s₀ := by
    have h2 : (0 : ℝ) < 2 ^ s₀ := by positivity
    have hh : κ ≤ (K : ℝ) / (2 : ℝ) ^ s₀ := (le_div_iff₀ h2).mpr hK
    simpa only [side, div_eq_mul_inv] using hh
  have hz : ∀ a, ∀ l ∈ A' a, ∀ jj : Fin (2 ^ s₀),
      ‖zc (Q (old a)) (c (old a)) (u (old a)) l (subMid (T i) s₀ (j (old a)) jj)‖ ≤ K * side s₀ := by
    intro a l hl jj
    exact (hzc a l hl _ (subblock_subset jj.isLt (subMid_mem (T i) s₀ (j (old a)) jj))).trans hKside
  have hdisj : ∀ a a', a ≠ a' → γ (old a) = γ (old a') → Disjoint (V a) (V a') :=
    hsi.2.2.2.2.2.2.2.2.2.2.1
  dsimp only
  refine ⟨measurableSet_rawCov old R' A' j c u Q R (T i) s₀ K V hformat hdeg hdegOld hVm, ?_, ?_, ?_⟩
  · intro e p hp
    exact ⟨hp.1, hp.2.1, subIco_subset _ _ _ _ hp.2.2⟩
  · intro e e' hne hworld
    exact rawCov_disjoint old R' A' j c u Q R (T i) s₀ K V γ hdisj hne hworld
  · calc
      _ = ∑ e, ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume)
          (entryIncidences old R' A' j c u Q R (T i) s₀ K V e) := by
        simp_rw [rawCov_eq_openEntryIncidences, openEntryIncidences_mass]
      _ = _ := weighted_entryIncidences_mass old R' A' j c u Q R (T i) s₀ K V γ ν
        (fun w => ENNReal.ofReal (ω w)) hformat hdeg hdegOld hVm hV hz

end
end Submission.Obl.k4_clean_cover_graph_atlas
