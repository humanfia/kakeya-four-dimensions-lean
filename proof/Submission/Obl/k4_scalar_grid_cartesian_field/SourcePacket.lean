import Submission.Obl.k4_scalar_grid_cartesian_field.QualifiedNonsteep
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketCoverage

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory MvPolynomial

/-- An actual qualified nonsteep packet of the unchanged original incidence law. -/
structure SourcePacket (data : Data) (k M : ℕ)
    (G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
    (E : (k : ℕ) → Fin (data.W k) → Set Incidence) (B ε L H : ℝ) where
  i : Fin (data.n k 1)
  original : OriginalPacketFacts data k i
  S : Set Incidence
  measurable_S : MeasurableSet S
  subset_E : S ⊆ E k (data.γ k 1 i)
  subset_packet : S ⊆ {x | x.1 ∈ data.A k 1 i ∧ x.2 ∈ I data (data.T k 1) (data.j k 1 i)}
  coefficients : ∀ x ∈ S, ∀ e, |x.1.2 e| ≤ data.K k
  qualified : ∀ x ∈ S, fit data k M G E B ε x i
  gradient : ∀ x ∈ S, ∀ e, |eval ![x.2, scalarY x.1 x.2] (pderiv e (data.F k 1 i))| ≤ L
  mass_floor : ENNReal.ofReal (1 / (8 * H)) *
    (ENNReal.ofReal (packetLength data k) * data.ν k (data.γ k 1 i) (data.A k 1 i)) ≤
      data.ρ k (data.γ k 1 i) S

/-- Select one original packet after the global qualification and steep deletions. -/
theorem source_packet_of_clean {data : Data} (hb : baseHyp data) {k M : ℕ}
    (G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
    (E : (k : ℕ) → Fin (data.W k) → Set Incidence) {B ε Q L : ℝ} (H : ℕ → ℝ)
    (hH : 1 ≤ H k) (hc : cleanPartsAt data M G E B H ε Q k)
    (hp : ∀ i : Fin (data.n k 1), OriginalPacketFacts data k i)
    (hcover : ∀ g : Fin (data.W k), data.ρ k g
      {x | ∃ i : Fin (data.n k 1), data.γ k 1 i = g ∧ x.1 ∈ data.A k 1 i ∧
        x.2 ∈ I data (data.T k 1) (data.j k 1 i)}ᶜ = 0)
    (hdisj : ∀ i i' : Fin (data.n k 1), i ≠ i' → data.γ k 1 i = data.γ k 1 i' →
      data.j k 1 i = data.j k 1 i' → Disjoint (data.A k 1 i) (data.A k 1 i'))
    (hgrad : ∀ (i : Fin (data.n k 1)) (x : Incidence), x.1 ∈ data.A k 1 i →
      x.2 ∈ I data (data.T k 1) (data.j k 1 i) → (∀ e, |x.1.2 e| ≤ data.K k) →
      x ∉ steepWorld data k (data.γ k 1 i) Q →
      ∀ e, |eval ![x.2, scalarY x.1 x.2] (pderiv e (data.F k 1 i))| ≤ L) :
    Nonempty (SourcePacket data k M G E B ε L (H k)) := by
  classical
  obtain ⟨Good, hGood, hmass⟩ := hc
  let μ : Fin (data.W k) → Measure Incidence := fun g => (data.ρ k g).restrict (Good g)
  let P : Fin (data.n k 1) → Set Incidence := fun i =>
    {x | x.1 ∈ data.A k 1 i ∧ x.2 ∈ I data (data.T k 1) (data.j k 1 i)}
  letI : ∀ g : Fin (data.W k), IsProbabilityMeasure (data.ν k g) := fun g => (hb k).2.2.1 g |>.1
  have hbudget := packet_prior_budget (data.ω k) (data.ν k) (data.γ k 1) (data.j k 1)
    (data.A k 1) (hb k).1 (hb k).2.1 (fun i => (hp i).measurable_A) hdisj
  have hbudget' : ∑ i : Fin (data.n k 1), ENNReal.ofReal (data.ω k (data.γ k 1 i)) *
      (ENNReal.ofReal (packetLength data k) * data.ν k (data.γ k 1 i) (data.A k 1 i)) ≤ 1 := by
    simpa only [packetLength, Submission.Obl.k4_scalar_noisy_block_packets.blockLength,
      ENNReal.ofReal_inv_of_pos (by positivity : 0 < (2 : ℝ) ^ data.T k 1)] using hbudget
  have hμcover (g : Fin (data.W k)) : μ g {x | ∃ i, data.γ k 1 i = g ∧ x ∈ P i}ᶜ = 0 := by
    have hμ : μ g ≤ data.ρ k g := Measure.restrict_le_self
    exact le_antisymm ((hμ _).trans_eq (hcover g)) bot_le
  have hHpos : 0 < H k := by linarith
  have hstrict : ENNReal.ofReal (1 / (8 * H k)) < ENNReal.ofReal (1 / (4 * H k)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 1 / (4 * H k))).mpr
    exact one_div_lt_one_div_of_lt (by positivity : 0 < 4 * H k) (by nlinarith)
  have hmass' : ENNReal.ofReal (1 / (8 * H k)) <
      ∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * μ g univ := by
    simpa only [μ, Measure.restrict_apply_univ] using hstrict.trans_le hmass
  obtain ⟨i, _, hi⟩ := exists_original_packet_with_retained_mass μ
    (fun g => ENNReal.ofReal (data.ω k g)) (data.γ k 1) P
    (fun i => ENNReal.ofReal (packetLength data k) * data.ν k (data.γ k 1 i) (data.A k 1 i))
    (ENNReal.ofReal (1 / (8 * H k))) hbudget' hμcover hmass'
  have hP : MeasurableSet (P i) := (hp i).measurable_A.prod measurableSet_Icc
  let S := Good (data.γ k 1 i) ∩ P i
  refine ⟨⟨i, hp i, S, (hGood _).1.inter hP, ?_, inter_subset_right, ?_, ?_, ?_, ?_⟩⟩
  · exact fun x hx => (hGood _).2.1 hx.1
  · exact fun x hx => ((hGood _).2.2 x hx.1).1
  · intro x hx
    by_contra hnot
    exact ((hGood _).2.2 x hx.1).2.1 ⟨i, rfl, hx.2.1, hx.2.2, hnot⟩
  · intro x hx
    exact hgrad i x hx.2.1 hx.2.2 ((hGood _).2.2 x hx.1).1 ((hGood _).2.2 x hx.1).2.2
  · simpa only [μ, Measure.restrict_apply hP, inter_comm, S] using hi

end Submission.Obl.k4_scalar_grid_cartesian_field
