import Submission.Obl.k4_scalar_grid_cartesian_field.SourcePacket
import Submission.Obl.k4_scalar_grid_cartesian_field.RegisteredSupport

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory MvPolynomial

/-- The original packet geometry applies on the selected source, with its low-gradient loss. -/
theorem SourcePacket.geometry {data : Data} {k M : ℕ}
    {G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    {E : (k : ℕ) → Fin (data.W k) → Set Incidence} {B ε L H : ℝ}
    (s : SourcePacket data k M G E B ε L H) (hN : 2 ≤ data.N k)
    (hκ : data.κ ≤ 1) (hL : 2 * data.K k ≤ L) :
    data.N k ^ (-1 : ℝ) ≤ L * packetLength data k ∧
    (∀ x ∈ s.S, ∀ e, |(![x.2, scalarY x.1 x.2] : Fin 2 → ℝ) e -
      originalOrigin data k s.i e| ≤ L * packetLength data k) ∧
    (∀ x ∈ s.S, |scalarX x.1 x.2 - eval ![x.2, scalarY x.1 x.2] (data.F k 1 s.i)| ≤
      L * data.N k ^ (-1 : ℝ)) := by
  have hNp : 0 < data.N k := by linarith
  have hK := s.original.budget_one
  have hKpos : 0 < data.K k := by linarith
  have hKL : data.K k ≤ L := by linarith
  have hh := s.original.positive_horizon
  refine ⟨?_, ?_, ?_⟩
  · have hδκ : data.N k ^ (-1 : ℝ) ≤ data.N k ^ (-data.κ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ data.N k) (by linarith)
    have hs := (div_le_iff₀ hKpos).mp s.original.horizon_lower
    have hδh : data.N k ^ (-1 : ℝ) ≤ data.K k * packetLength data k := by nlinarith
    exact hδh.trans (mul_le_mul_of_nonneg_right hKL hh.le)
  · intro x hx e
    have hp := s.subset_packet hx
    have hn := s.original.normalized_bound x.1 hp.1 x.2 hp.2 e
    change |((![x.2, scalarY x.1 x.2] : Fin 2 → ℝ) e - originalOrigin data k s.i e) /
      packetLength data k| ≤ 2 * data.K k at hn
    rw [abs_div, abs_of_pos hh] at hn
    exact ((div_le_iff₀ hh).mp hn).trans (mul_le_mul_of_nonneg_right hL hh.le)
  · intro x hx
    have hp := s.subset_packet hx
    exact ((s.original.fit x.1 hp.1 x.2 hp.2).2).trans
      (mul_le_mul_of_nonneg_right hKL (Real.rpow_nonneg hNp.le _))

/-- Every later submeasure of the source has the sharp joint support bound at all hidden widths. -/
theorem SourcePacket.joint_support {data : Data} {k M : ℕ}
    {G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    {E : (k : ℕ) → Fin (data.W k) → Set Incidence} {B ε L H H₀ : ℝ}
    (s : SourcePacket data k M G E B ε L H) (hN : 2 ≤ data.N k) (hκ : data.κ ≤ 1)
    (hd : 0 ≤ data.d) (hdone : data.d ≤ 1) (hH₀ : 1 ≤ H₀) (hL : 2 * data.K k ≤ L)
    (m : ℕ) (hm : 1 ≤ m) (hstep : data.N k ^ (1 / (m : ℝ)) ≤ H₀)
    (E₀ : Set Incidence) (hsource : s.S ⊆ E₀) {R : ℝ} (hR : 3 ≤ R)
    (hprep : RegisteredSupportControl ((data.ρ k (data.γ k 1 s.i)).restrict E₀)
      (fun x => ![x.2, scalarY x.1 x.2]) (fun x => scalarX x.1 x.2)
      (data.N k) H₀ data.d m R)
    (μ : Measure Incidence) (hμ : μ ≤ (data.ρ k (data.γ k 1 s.i)).restrict s.S)
    (hhor : data.N k ^ (-2 : ℝ) ≤ packetLength data k)
    (w : ℝ) (hwlo : data.N k ^ (-1 : ℝ) * packetLength data k ^ ((1 : ℝ) / 8) ≤ w)
    (hwhi : w ≤ data.N k ^ (-1 : ℝ)) :
    (activeCodes μ (fun x =>
      ((fun e : Fin 2 => (⌊normalizedBase (packetLength data k) (originalOrigin data k s.i) x e /
        data.N k ^ (-10 : ℝ)⌋ : ℤ)), (⌊scalarX x.1 x.2 / w⌋ : ℤ)))).Finite ∧
    ((activeCodes μ (fun x =>
      ((fun e : Fin 2 => (⌊normalizedBase (packetLength data k) (originalOrigin data k s.i) x e /
        data.N k ^ (-10 : ℝ)⌋ : ℤ)), (⌊scalarX x.1 x.2 / w⌋ : ℤ)))).ncard : ℝ) ≤
      (32000 * L ^ 3 * H₀ ^ 2) * data.N k ^ (20 : ℝ) * (data.N k ^ (-1 : ℝ) / w) ^ data.d := by
  have hNp : 0 < data.N k := by linarith
  have hK := s.original.budget_one
  have hLone : 1 ≤ L := by linarith
  have hμE : μ ≤ (data.ρ k (data.γ k 1 s.i)).restrict E₀ :=
    hμ.trans (Measure.restrict_mono_set _ hsource)
  have hsupp : μ s.Sᶜ = 0 := le_antisymm
    ((hμ s.Sᶜ).trans_eq (ae_iff.mp (ae_restrict_mem s.measurable_S))) bot_le
  obtain ⟨hscale, hbase, hfit⟩ := s.geometry hN hκ hL
  have hsmall := fine_base_mesh_small (by linarith : 1 ≤ data.N k) s.original.bounded_horizon
  have hw := hidden_width_fixed_range hN hhor hwlo
  have h := registered_packet_joint_count ((data.ρ k (data.γ k 1 s.i)).restrict E₀) μ hμE
    s.S hsupp (fun x => ![x.2, scalarY x.1 x.2]) (fun x => scalarX x.1 x.2)
    (data.F k 1 s.i) s.original.quadratic hN hH₀ hm hstep hd hdone s.original.positive_horizon
    hLone hscale hR (Real.rpow_pos_of_pos hNp _) hsmall (originalOrigin data k s.i)
    hbase hfit s.gradient hprep hw hwhi
  have hξ : ((data.N k ^ (-10 : ℝ))⁻¹) ^ 2 = data.N k ^ (20 : ℝ) := by
    rw [← Real.rpow_neg hNp.le, ← Real.rpow_mul_natCast hNp.le]
    norm_num
  simpa only [normalizedBase, hξ] using h

end Submission.Obl.k4_scalar_grid_cartesian_field
