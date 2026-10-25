import Submission.Obl.k4_scalar_grid_cartesian_field.PacketSteepMass
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketCoverage
import Submission.Obl.k4_scalar_grid_cartesian_field.Growth

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter MvPolynomial

noncomputable def steepWorld (data : Data) (k : ℕ) (g : Fin (data.W k)) (Q : ℝ) : Set Incidence :=
  {x | ∃ i : Fin (data.n k 1), data.γ k 1 i = g ∧ x ∈ steepPacket data k i Q}

/-- Steep packet deletion is an actual original measurable incidence event. -/
theorem measurableSet_steepPacket {data : Data} {k : ℕ} {i : Fin (data.n k 1)}
    (p : OriginalPacketFacts data k i) (Q : ℝ) : MeasurableSet (steepPacket data k i Q) := by
  have hA : MeasurableSet {x : Incidence | x.1 ∈ data.A k 1 i} := p.measurable_A.preimage measurable_fst
  have hI : MeasurableSet {x : Incidence | x.2 ∈ I data (data.T k 1) (data.j k 1 i)} := by
    exact measurableSet_Icc.preimage measurable_snd
  have hcoeff : MeasurableSet {x : Incidence | ∀ e, |x.1.2 e| ≤ data.K k} :=
    (measurableSet_coefficient_bound (data.K k)).preimage measurable_fst
  have hg := ((MvPolynomial.continuous_eval (pderiv 1 (data.F k 1 i))).measurable.comp
    measurable_scalar_base).abs
  exact hA.inter (hI.inter (hcoeff.inter (measurableSet_le measurable_const hg)))

/-- A finite original world union keeps the measurable steep event. -/
theorem measurableSet_steepWorld (data : Data) (k : ℕ)
    (h : ∀ i : Fin (data.n k 1), OriginalPacketFacts data k i)
    (g : Fin (data.W k)) (Q : ℝ) : MeasurableSet (steepWorld data k g Q) := by
  have heq : steepWorld data k g Q = ⋃ i : Fin (data.n k 1), ⋃ _ : data.γ k 1 i = g,
      steepPacket data k i Q := by ext x; simp [steepWorld]
  rw [heq]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => measurableSet_steepPacket (h i) Q

/-- Steep deletion is power-small in the TOTAL original weighted incidence law.
The number of packet labels cancels through the original full-prior assignment budget. -/
theorem global_steep_mass_bound (data : Data) (hs : scaleHyp data) (hb : baseHyp data)
    (hcap : capHyp data) (hpacket : packetHyp data) {b : ℝ} (hbpos : 0 < b) :
    ∀ᶠ k in atTop,
      (∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) *
        data.ρ k g (steepWorld data k g (data.N k ^ (2 * b)))) ≤
      ENNReal.ofReal (400000 * data.K k ^ 11 * data.N k ^ (-data.S * b)) := by
  have hN₁ : ∀ k, 1 ≤ data.N k := fun k => by linarith [hs.1 k]
  have hκ : 0 < data.κ := hs.2.2.2.2.2.1
  have hκone : data.κ ≤ 1 := hs.2.2.2.2.2.2.1
  have hK := hs.2.2.1
  let R := max 12 (max b (2 / b))
  have hR : 1 < R := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 12) (le_max_left _ _)
  have hRb : 2 / b ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hbR : b ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRinvb : R⁻¹ ≤ b := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < R)]
    have h := (div_le_iff₀ hbpos).mp hRb
    nlinarith
  have hRinvone : R⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hR.le
  have hRspatiallo : R⁻¹ ≤ 10 + data.κ := hRinvone.trans (by linarith)
  have hRspatialhi : 10 + data.κ ≤ R := by have := le_max_left (12 : ℝ) (max b (2 / b)); linarith
  have hFnum := eventually_polynomial_subpower_le hN₁ hs.2.1 hK
    (by norm_num : (1 : ℝ) ≤ 2880) 3 (by norm_num : (0 : ℝ) < 9)
  have hGnum := eventually_polynomial_subpower_le hN₁ hs.2.1 hK
    (by norm_num : (1 : ℝ) ≤ 23040) 5 (by norm_num : (0 : ℝ) < 9)
  have hsep := eventually_polynomial_subpower_le hN₁ hs.2.1 hK
    (by norm_num : (1 : ℝ) ≤ 32) 2 hbpos
  filter_upwards [hcap R hR, hpacket 2 (by norm_num), original_packet_facts_eventually data hs hb hpacket,
    hFnum, hGnum, hsep] with k hcapk hpackk hfacts hF hG hsep
  classical
  letI : ∀ g : Fin (data.W k), IsProbabilityMeasure (data.ν k g) := fun g => (hb k).2.2.1 g |>.1
  obtain ⟨_, _, hA, hdisj, _, _⟩ := hpackk 1 (by norm_num) (by norm_num)
  have hbudget := packet_prior_budget (data.ω k) (data.ν k) (data.γ k 1) (data.j k 1)
    (data.A k 1) (hb k).1 (hb k).2.1 hA hdisj
  have hbudget' : ∑ i : Fin (data.n k 1), ENNReal.ofReal (data.ω k (data.γ k 1 i)) *
      (ENNReal.ofReal (packetLength data k) * data.ν k (data.γ k 1 i) (data.A k 1 i)) ≤ 1 := by
    simpa only [packetLength, Submission.Obl.k4_scalar_noisy_block_packets.blockLength,
      ENNReal.ofReal_inv_of_pos (by positivity : 0 < (2 : ℝ) ^ data.T k 1)] using hbudget
  have hmass (i : Fin (data.n k 1)) :
      data.ρ k (data.γ k 1 i) (steepPacket data k i (data.N k ^ (2 * b))) ≤
        ENNReal.ofReal (400000 * data.K k ^ 11 * data.N k ^ (-data.S * b)) *
          (ENNReal.ofReal (packetLength data k) * data.ν k (data.γ k 1 i) (data.A k 1 i)) := by
    obtain ⟨hπ, _, hρ⟩ := hcapk (data.γ k 1 i) (10 + data.κ) 1 b
      hRspatiallo hRspatialhi hRinvone hR.le hRinvb hbR
    apply packet_steep_mass_bound (hfacts i) (hs.1 k) hκone hbpos hF hG hsep
    · simpa only [vel] using hπ
    · simpa only [x_eq_scalarX, mul_one, vel, Set.mem_ofPred_eq] using hρ
  let C := ENNReal.ofReal (400000 * data.K k ^ 11 * data.N k ^ (-data.S * b))
  calc
    _ ≤ ∑ i : Fin (data.n k 1), ENNReal.ofReal (data.ω k (data.γ k 1 i)) *
        data.ρ k (data.γ k 1 i) (steepPacket data k i (data.N k ^ (2 * b))) :=
      weighted_packet_union_mass (data.ρ k) (fun g => ENNReal.ofReal (data.ω k g))
        (data.γ k 1) (fun i => steepPacket data k i (data.N k ^ (2 * b)))
    _ ≤ ∑ i : Fin (data.n k 1), ENNReal.ofReal (data.ω k (data.γ k 1 i)) *
        (C * (ENNReal.ofReal (packetLength data k) * data.ν k (data.γ k 1 i) (data.A k 1 i))) :=
      Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (hmass i)
    _ = C * ∑ i : Fin (data.n k 1), ENNReal.ofReal (data.ω k (data.γ k 1 i)) *
        (ENNReal.ofReal (packetLength data k) * data.ν k (data.γ k 1 i) (data.A k 1 i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ac_rfl
    _ ≤ C * 1 := mul_le_mul' le_rfl hbudget'
    _ = _ := mul_one C

end Submission.Obl.k4_scalar_grid_cartesian_field
