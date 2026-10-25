import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Sequence
import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.DecodedTypical
import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.VaryingJoint
import Submission.Obl.k4_remainder_pure_profile_normalization.HomogeneousSelection
import Submission.Obl.k4_joint_homogenization

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Encode all worlds into a single tempered world, apply the accepted
homogenization theorem, and pull back its incidence selection. -/
theorem pureHomogenization : PureHomogenization := by
  classical
  intro p hN ht hK hL hs
  obtain ⟨M,D,hs⟩ := hs
  obtain ⟨M₀,hM₀⟩ :=
    Submission.Obl.k4_scalar_marked_coefficient_smoothing.uniform_nat_exponent hN
      (hK.2 1 (by norm_num))
  have hpow (k : ℕ) : p.K k ≤ p.N k ^ M₀ := by
    simpa only [Real.rpow_natCast] using hM₀ k
  let S := encodedSample p M M₀
  have hS (k : ℕ) : (S k).Hyp := encodedSample_hyp k (hs k) (hN k) (hK.1 k) (hpow k)
  have hT (k : ℕ) : Tempered (S k).N (S k).K M D (S k).W
      (S k).ω (S k).ν (S k).E (S k).B := tempered_of_sample (hs k)
  have hN1 (k : ℕ) : 1 ≤ p.N k := by linarith [hN k]
  have hKe := encoding_subpower hN1 ht hK
  let r₀ : ℝ := ((2 * M + 2 : ℕ) : ℝ)
  let R : ℝ := r₀ + p.L + 1
  have hr₀ : 0 ≤ r₀ := by dsimp [r₀]; positivity
  have hR : 0 < R := by dsimp [R]; linarith
  obtain ⟨ψ,hψ,K',E',hK',hsub,hfmt',F,hF,hd,htyp⟩ :=
    Submission.k4_joint_homogenization p.N (fun k => 2 * p.K k + 6) hN ht hKe
      (fun k => (S k).prior) (fun k => (S k).event)
      (encodedFamily_format hs hS) R 1 hR (by norm_num)
  obtain ⟨M',D',hfmt'⟩ := hfmt'
  have he (k : ℕ) : MeasurableSet (E' k) := (hfmt' k).2.2.1
  have hE (k : ℕ) : E' k ⊆ (S (ψ k)).event := (hsub k).2
  let E₂ := fun k => (S (ψ k)).decEvent (E' k)
  let K₂ := fun k => max (p.K (ψ k)) (K' k)
  have hs₂ (k : ℕ) : Normalization.SampleProblem (p.N (ψ k)) (K₂ k)
      (max M M') (max D D') (p.W (ψ k)) (p.ω (ψ k)) (p.ν (ψ k))
      (E₂ k) (p.P (ψ k)) (p.B (ψ k)) :=
    (hS (ψ k)).decoded_sample (hs (ψ k)) (he k) (hE k)
      (hfmt' k).2.2.2.2.2.1 (hfmt' k).2.2.2.2.2.2.2
      (by linarith [hK'.1 k])
  choose g hg using fun k (b : Fin (p.W (ψ k))) (s : ℝ) =>
    (hs (ψ k)).pure_density (hN (ψ k)) b (E₂ k b) (δ (p.N (ψ k)) s)
  choose G hG using fun k (b : Fin (p.W (ψ k))) (u : ℝ) =>
    (hs (ψ k)).joint_density (hN (ψ k)) b (E₂ k b)
      (δ (p.N (ψ k)) p.L) (δ (p.N (ψ k)) u)
  let f : ℝ → ℝ := fun s => F (r₀ + s) 0 + ((M + 2 * M₀ + 4 : ℕ) : ℝ)
  let sel : IncidenceSelection p := ⟨ψ,hψ,K₂,E₂,f,g,G⟩
  have hK₂ : Submission.Obl.k4_joint_homogenization.Subpower (p.N ∘ ψ) K₂ :=
    Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max
      (Submission.Obl.k4_joint_homogenization.subpower_comp hK hψ) hK'
  refine ⟨⟨sel,fun k => le_max_left _ _,fun k b => (hS (ψ k)).decEvent_subset (hE k) b,
    hK₂,⟨max M M',max D D',hs₂⟩,?_,?_,?_,?_⟩⟩
  · intro k b s _ _
    exact ⟨(hg k b s).1,(hg k b s).2.1⟩
  · intro k b u _ _
    exact ⟨(hG k b u).1,(hG k b u).2.1⟩
  · intro s t hs0 hst htL
    have H := hF.1 (r₀ + s) (r₀ + t) 0 (by linarith) (by linarith)
      (by dsimp [R]; linarith) le_rfl (by norm_num)
    change 0 ≤ f t - f s ∧ f t - f s ≤ t - s
    dsimp [f]
    constructor <;> linarith [H.1,H.2]
  · intro s hs0 hsL
    let n : ℕ → ℝ := p.N ∘ ψ
    let μ : ℕ → Measure Incidence :=
      fun k => ((S (ψ k)).prior.prod volume).restrict (E' k)
    have hn (k : ℕ) : 1 ≤ n k := hN1 (ψ k)
    have hn' (k : ℕ) : 1 < n k := by dsimp [n]; linarith [hN (ψ k)]
    have hnt : Tendsto n atTop atTop := ht.comp hψ.tendsto_atTop
    have hμ : ∀ k, μ k univ ≤ 1 :=
      Submission.Obl.k4_joint_homogenization.law_le_one ⟨M',D',hfmt'⟩
    have : ∀ k, IsFiniteMeasure (μ k) := fun k => ⟨(hμ k).trans_lt ENNReal.one_lt_top⟩
    let a : ℕ → ℝ := fun k => depthSum (n k) r₀ s
    have ha (k : ℕ) : a k ∈ Icc (0 : ℝ) R :=
      ⟨depthSum_nonneg (hn' k) hr₀ hs0,
        (depthSum_le (hn' k) r₀ s).trans (by dsimp [R]; linarith)⟩
    have har : r₀ + s ∈ Icc (0 : ℝ) R :=
      ⟨by linarith,by dsimp [R]; linarith⟩
    have hat : Tendsto a atTop (𝓝 (r₀ + s)) := depthSum_tendsto hn' hnt r₀ s
    let ge := fun k => (S (ψ k)).encDensity (fun b => g k b s)
    have hge (k : ℕ) : Measurable (ge k) :=
      (S (ψ k)).measurable_encDensity (fun b => (hg k b s).1)
    have hgelaw (k : ℕ) : (μ k).map (jointObs (n k) (a k) 0) =
        jointRef.withDensity (ge k) :=
      (hS (ψ k)).encoded_density_law (hT (ψ k)) (he k) (hE k) s
        (fun b => (hg k b s).1) (fun b => (hg k b s).2.1)
    have H := typical_joint_at_tendsto_depth n hn hnt μ hR.le F hF hd htyp
      a ha har hat ge hge hgelaw
    exact decoded_typical (fun k => hS (ψ k)) (fun k => hT (ψ k)) (fun _ => rfl)
      E' he hE s (F (r₀ + s) 0) (fun k b => g k b s)
      (fun k b => (hg k b s).1) H

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
