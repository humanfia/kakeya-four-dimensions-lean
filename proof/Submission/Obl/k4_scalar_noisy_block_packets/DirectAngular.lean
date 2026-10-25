import Submission.Obl.k4_scalar_noisy_block_packets.Interface

namespace Submission.Obl.k4_scalar_noisy_block_packets

open MeasureTheory Set Filter
open scoped ENNReal

/-- The exact theorem's bounded polynomial sign format. -/
def Format (n : ℕ) (B : ℝ) (D : ℕ) (A : Set (Fin n → ℝ)) : Prop :=
  ∃ k : ℕ, (k : ℝ) ≤ B ∧ ∃ p : Fin k → MvPolynomial (Fin n) ℝ,
    (∀ j, (p j).totalDegree ≤ D ∧ ∀ b, |(p j).coeff b| ≤ B) ∧
    ∃ S : Set (Fin k → SignType), A = {x | (fun j => SignType.sign (MvPolynomial.eval x (p j))) ∈ S}

noncomputable def selected (ν : Measure Line) (E : Set Inc) : Measure Inc :=
  (ν.prod volume).restrict E

/-- Bounded semialgebraic input with one world. -/
def SingleInput (N K : ℕ → ℝ) (M D : ℕ) (ν : ℕ → Measure Line)
    (E : ℕ → Set Inc) : Prop :=
  ∀ k, IsProbabilityMeasure (ν k) ∧
    (∃ n : ℕ, (n : ℝ) ≤ N k ^ (M : ℝ) ∧
      ∃ (h : Fin n → ℝ) (i : Fin n → ℕ) (B : Fin n → Set (Fin 5 → ℝ)),
        (∀ j, 0 ≤ h j ∧ h j ≤ N k ^ (M : ℝ) ∧ (i j : ℝ) ≤ N k ^ (M : ℝ) ∧
          Format 5 (N k ^ (M : ℝ)) D (B j) ∧ ∀ b ∈ B j, ∀ e, |b e| ≤ N k ^ (M : ℝ)) ∧
        ν k = ∑ j, ENNReal.ofReal (h j) • Measure.map (fun b => (i j, b)) (volume.restrict (B j))) ∧
    (∀ᵐ l ∂ν k, ∀ e, |l.2 e| ≤ K k) ∧ MeasurableSet (E k) ∧
    E k ⊆ univ ×ˢ Icc (0 : ℝ) 1 ∧
    (∀ p ∈ E k, (p.1.1 : ℝ) ≤ N k ^ (M : ℝ)) ∧
    (∀ i : ℕ, Format 6 (N k ^ (M : ℝ)) D {b | ((i, fun e : Fin 5 => b e.castSucc), b 5) ∈ E k}) ∧
    ENNReal.ofReal ((K k)⁻¹) ≤ selected (ν k) (E k) univ

/-- The finite packet conclusion before selecting one common block. -/
def ExactOutput (N L fL h ε : ℝ) (μ : Measure Inc) : Prop :=
  ∃ (T n : ℕ) (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set Line)
      (P : Fin n → MvPolynomial (Fin 2) ℝ),
    (2 : ℝ) ^ T ≤ N ^ h ∧ (∀ i, MeasurableSet (A i)) ∧
    (∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i')) ∧
    (∀ i, (P i).totalDegree ≤ 2 ∧
      (∀ t ∈ Icc ((j i : ℝ) / (2 : ℝ) ^ T) (((j i : ℝ) + 1) / (2 : ℝ) ^ T),
        ∀ w ∈ Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, w] (P i)| ≤ N ^ ε) ∧
      (∀ l ∈ A i, ∀ t ∈ Icc ((j i : ℝ) / (2 : ℝ) ^ T) (((j i : ℝ) + 1) / (2 : ℝ) ^ T),
        |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N ^ ε * N ^ (-L)) ∧
      ENNReal.ofReal (N ^ (-fL) / (N ^ ε * (2 : ℝ) ^ T)) ≤
        μ (A i ×ˢ Icc ((j i : ℝ) / (2 : ℝ) ^ T) (((j i : ℝ) + 1) / (2 : ℝ) ^ T))) ∧
    ENNReal.ofReal (N ^ (-ε)) ≤
      μ {p | ∃ i, p.1 ∈ A i ∧ p.2 ∈ Icc ((j i : ℝ) / (2 : ℝ) ^ T)
        (((j i : ℝ) + 1) / (2 : ℝ) ^ T)}

theorem profile_endpoint_cap {d s m S U C₀ r : ℝ} {angular : Bool} {F : ℝ → ℝ → ℝ}
    (h : ProfileShape d s m S U C₀ angular F) (hr : 0 ≤ r) (hrs : r ≤ s)
    (hV : 0 ≤ 4 * (m + s + 1)) :
    F s 0 - F r 0 ≤ d * (s - r) := by
  rcases h with ⟨_, _, hend, hlo, _⟩
  have hl := hlo r 0 hr hrs le_rfl hV
  rw [hend] at *
  have hm : 0 ≤ max (0 : ℝ) (0 - m) := le_max_left _ _
  nlinarith

/-- With the optional angular bound, no crop is needed to apply the exact assertion. -/
theorem direct_exact_packets
    (hexact : ExactAngularPackets) (N K : ℕ → ℝ)
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop) (hK : Subpower N K)
    (M D : ℕ) (hM : 1 ≤ M) (hD : 1 ≤ D)
    (d s m S U C₀ : ℝ) {F : ℝ → ℝ → ℝ} (hd : 0 ≤ d) (hd1 : d < 1) (hs : 0 < s)
    (hS : 0 < S) (hU : 0 < U) (hUV : U ≤ 4 * (m + s + 1))
    (ν : ℕ → Measure Line) (E : ℕ → Set Inc)
    (hin : SingleInput N K M D ν E)
    (hshape : ProfileShape d s m S U C₀ true F)
    (hhom : Homogeneous N s (4 * (m + s + 1)) (fun k => selected (ν k) (E k)) F)
    (h ε : ℝ) (hh : 0 < h) (hε : 0 < ε) :
    ∃ᶠ k in atTop, ExactOutput (N k) s (F s 0) h ε (selected (ν k) (E k)) := by
  classical
  rcases hhom with ⟨g, G, hg, hG, htyp, htypG⟩
  have hV : 0 ≤ 4 * (m + s + 1) := hU.le.trans hUV
  have hout := hexact N K hN hNt hK M D s d S U hM hD hs hd hd1 hS hU
    (fun _ => 1) (fun _ _ => 1) (fun k _ => ν k) (fun k _ => E k)
    (fun k _ => g k) (fun k _ => G k s) (fun r => F r 0)
  have hin' : ∀ k, (1 : ℝ) ≤ N k ^ (M : ℝ) := fun k =>
    Real.one_le_rpow (by linarith [hN k]) (by positivity)
  specialize hout (by
    intro k
    rcases hin k with ⟨hp, hfmt, hbound, hmeas, hsub, htag, hslice, hmass⟩
    refine ⟨by simpa using hin' k, (fun _ => zero_le_one), by simp, ?_, ?_⟩
    · intro γ
      exact ⟨hp, hfmt, hbound, hmeas, hsub, htag, hslice⟩
    · simpa only [Fin.sum_univ_one, ENNReal.ofReal_one, one_mul, selected] using hmass)
    (by simpa only [x, y, selected] using fun k (_ : Fin 1) r hr hrs => hg k r hr hrs)
    (by
      intro k γ u hu huU
      simpa only [x, y, selected] using hG k s u hs.le le_rfl hu.le (huU.trans hUV))
    (by
      intro r r' hr hrr' hr's
      exact hshape.1 r r' 0 hr hrr' hr's le_rfl hV)
    (by
      intro r τ hr hrs hτ
      obtain ⟨a, ha, hea⟩ := htyp r τ hr hrs hτ
      refine ⟨a, ha, ?_⟩
      simpa only [Fin.sum_univ_one, ENNReal.ofReal_one, one_mul, x, y, selected] using hea)
    (fun r hr hrs => profile_endpoint_cap hshape hr hrs hV)
    (by
      intro u τ hu huU hτ
      obtain ⟨a, ha, hea⟩ := htypG s u τ hs.le le_rfl hu.le (huU.trans hUV) hτ
      refine ⟨a, ha, ?_⟩
      filter_upwards [hea] with k hk
      simp only [Fin.sum_univ_one, ENNReal.ofReal_one, one_mul]
      apply le_trans (measure_mono ?_) hk
      intro p hp
      apply Or.inr
      have he := hshape.2.2.2.2 rfl u hu.le huU
      exact (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le
        (by linarith [hN k]) (by linarith))).trans_lt hp)
    h ε hh hε
  apply hout.mono
  intro k hk
  rcases hk with ⟨T, n, γ, j, A, P, hb, hA, hdis, hfit, hmass⟩
  refine ⟨T, n, j, A, P, hb, hA, ?_, hfit, ?_⟩
  · intro i i' hne hji
    exact hdis i i' hne (Subsingleton.elim _ _) hji
  · simpa only [Fin.sum_univ_one, ENNReal.ofReal_one, one_mul, Fin.eq_zero, true_and, selected] using hmass

end Submission.Obl.k4_scalar_noisy_block_packets
