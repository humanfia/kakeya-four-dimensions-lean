import Submission.Obl.k4_scalar_noisy_block_packets.CropInterface
import Submission.Obl.k4_scalar_noisy_block_packets.CropLift
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_scalar_noisy_block_packets

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

/-- Package the concrete scalar-crop identities for the finite lifting theorem. -/
def liftData {N : ℕ → ℝ} {u₀ : ℝ} {W : ℕ → ℕ}
    {ν₀ : ℕ → Measure Line} {E₀ : ℕ → Set Inc}
    {ν : (k : ℕ) → Fin (W k) → Measure Line} {E : (k : ℕ) → Fin (W k) → Set Inc}
    {p : (k : ℕ) → Fin (W k) → ℝ} {z : (k : ℕ) → Fin (W k) → Fin 2 → ℤ}
    (hf : LiftFacts N u₀ W ν₀ E₀ ν E p z) (k : ℕ) :
    CropLiftData (W k) (N k ^ (-u₀)) (selected (ν₀ k) (E₀ k))
      (fun γ => selected (ν k γ) (E k γ)) where
  crop := fun γ => scalarCell (N k) u₀ (z k γ)
  phi := fun γ => scalarCropLine (N k) u₀ (z k γ)
  prior := p k
  u := fun γ => N k ^ (-u₀) * (z k γ 0 : ℝ)
  v := fun γ => N k ^ (-u₀) * (z k γ 1 : ℝ)
  measurable_crop := hf.1 k
  measurable_phi := hf.2.1 k
  disjoint_crop := hf.2.2.1 k
  law := hf.2.2.2.1 k
  x_eq := hf.2.2.2.2.1 k
  y_eq := hf.2.2.2.2.2.1 k
  y_bound := hf.2.2.2.2.2.2 k

/-- Applying the assumed exact assertion involves no further crop or density argument. -/
theorem exact_of_worlds (hexact : ExactAngularPackets)
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : Subpower N K) (L d S U : ℝ)
    (hL : 0 < L) (hd : 0 ≤ d) (hd1 : d < 1) (hS : 0 < S) (hU : 0 < U)
    (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set Inc) (f : ℝ → ℝ)
    (hw : AngularWorlds N K L d S U W ω ν E f)
    (h ε : ℝ) (hh : 0 < h) (hε : 0 < ε) :
    ∃ᶠ k in atTop, MultiExactOutput (N k) L (f L) h ε (W k) (ω k)
      (fun γ => selected (ν k γ) (E k γ)) := by
  rcases hw with ⟨⟨M, D, hM, hD, hfmt⟩, g, G, hg, hG, hmono, htyp, hcap, hang⟩
  have hout := hexact N K hN hNt hK M D L d S U hM hD hL hd hd1 hS hU
    W ω ν E g G f hfmt hg hG hmono htyp hcap hang h ε hh hε
  simpa only [MultiExactOutput, blockInterval_eq, selected, x, y] using hout

/-- All exponent losses after the crop has been constructed are elementary. -/
theorem lift_prepared
    (hexact : ExactAngularPackets) (N K : ℕ → ℝ)
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop) (hK : Subpower N K)
    (ν₀ : ℕ → Measure Line) (E₀ : ℕ → Set Inc)
    (d s m C₀ η L u₀ d' S' U' α : ℝ) (angular : Bool)
    (F : ℝ → ℝ → ℝ) (c : ℕ → ℝ)
    (_hd : 0 ≤ d) (_hd1 : d < 1) (_hs : 0 < s) (_hsm : s < m) (hη : 0 < η)
    (he : EndpointData d s m C₀ angular η F L u₀ d' S' U')
    (hc : ∀ τ : ℝ, 0 < τ → ∀ᶠ k in atTop,
      N k ^ (C₀ - τ) ≤ c k ∧ c k ≤ N k ^ (C₀ + τ))
    (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set Inc)
    (p : (k : ℕ) → Fin (W k) → ℝ)
    (z : (k : ℕ) → Fin (W k) → Fin 2 → ℤ) (ρ : ℕ → ℝ)
    (hcrop : ScalarCrops N K ν₀ E₀ u₀ α W ω ν E p z ρ)
    (hw : AngularWorlds N K L d' S' U' W ω ν E (fun r => F r u₀ + u₀ - α))
    (ε : ℝ) (hε : 0 < ε) (hbudget : 20 * η < ε) :
    ∃ᶠ k in atTop, NoisyOutput (N k) d s m (c k) ε angular (selected (ν₀ k) (E₀ k)) := by
  rcases he with ⟨hL, hLs, hu, hum, hd', hd'1, hS', hU', hUV, hnear, hF, hfull, hcap, hang⟩
  rcases hcrop with ⟨hsrc, hz, hp, hρ, hρsub, hpsub, hf⟩
  have hout := exact_of_worlds hexact N K hN hNt hK L d' S' U'
    hL hd' hd'1 hS' hU' W ω ν E (fun r => F r u₀ + u₀ - α) hw η η hη hη
  have hbig : ∀ᶠ k in atTop, 2 ≤ N k ^ ε := by
    filter_upwards [k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt hε 2] with k hk
    simpa only [Real.rpow_zero, mul_one] using hk.le
  apply (hout.and_eventually ((hc η hη).and ((hpsub η hη).and
    ((hρsub η hη).and ((hK.2 ε hε).and hbig))))).mono
  intro k hk
  rcases hk with ⟨hkout, hck, hpk, hρk, hKk, hbigk⟩
  have hn : 1 ≤ N k := by linarith [hN k]
  have hn0 : 0 < N k := by linarith
  have hpow (a b : ℝ) (hab : a ≤ b) : N k ^ a ≤ N k ^ b :=
    Real.rpow_le_rpow_of_exponent_le hn hab
  have hρlo : N k ^ (-η) ≤ ρ k := by
    have hpos := (hρ k).1
    rw [Real.rpow_neg hn0.le]
    exact (inv_le_comm₀ (Real.rpow_pos_of_pos hn0 _) hpos).2 hρk
  apply noisyOutput_of_crop_exact (N k) d s m (c k) ε L (F L u₀ + u₀ - α)
    η η (N k ^ (-u₀)) (ρ k) angular (W k) (ω k)
    (selected (ν₀ k) (E₀ k)) (fun γ => selected (ν k γ) (E k γ)) (liftData hf k)
    hn (Real.rpow_pos_of_pos hn0 _) (by linarith) hbigk
  · rw [← Real.rpow_neg hn0.le]
    exact hpow _ _ (by linarith)
  · rw [← Real.rpow_sub hn0]
    exact hpow _ _ (by linarith)
  · exact (hpow _ 0 (by linarith)).trans (by simpa using (show 1 ≤ N k ^ ε by linarith))
  · intro ha
    rw [hfull ha, neg_zero, Real.rpow_zero]
    exact (hpow _ 0 (by linarith)).trans_eq (Real.rpow_zero _)
  · intro γ
    exact (hp k γ).2.2.2.2.trans hKk
  · exact fun γ => (hp k γ).1.le
  · intro γ
    change ENNReal.ofReal (p k γ) = ENNReal.ofReal (ρ k) * ENNReal.ofReal (ω k γ)
    rw [(hρ k).2.2.2 γ, ← ENNReal.ofReal_mul (hρ k).1.le]
    congr 1
    field_simp [(hρ k).1.ne']
  · intro γ
    change c k * (N k ^ (-s)) ^ d * N k ^ (-u₀) / N k ^ ε ≤
      p k γ * N k ^ (-(F L u₀ + u₀ - α)) / N k ^ η
    calc
      _ ≤ N k ^ (C₀ + η) * (N k ^ (-s)) ^ d * N k ^ (-u₀) / N k ^ ε := by
        gcongr
        exact hck.2
      _ = N k ^ (C₀ + η - s * d - u₀ - ε) := by
        rw [← Real.rpow_mul hn0.le, ← Real.rpow_add hn0, ← Real.rpow_add hn0,
          ← Real.rpow_sub hn0]
        congr 1
        ring
      _ ≤ N k ^ (-α - η - (F L u₀ + u₀ - α) - η) := hpow _ _ (by linarith)
      _ = N k ^ (-α - η) * N k ^ (-(F L u₀ + u₀ - α)) / N k ^ η := by
        rw [← Real.rpow_add hn0, ← Real.rpow_sub hn0]
        congr 1
      _ ≤ _ := by
        gcongr
        exact (hpk γ).1
  · calc
      _ = N k ^ (-ε + η) := by rw [← Real.rpow_add hn0]
      _ ≤ N k ^ (-η - η) := hpow _ _ (by linarith)
      _ = N k ^ (-η) * N k ^ (-η) := by rw [← Real.rpow_add hn0]; ring_nf
      _ ≤ ρ k * N k ^ (-η) := mul_le_mul_of_nonneg_right hρlo (by positivity)
  · rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
    exact hpow _ _ (by linarith)
  · exact hkout

end
end Submission.Obl.k4_scalar_noisy_block_packets
