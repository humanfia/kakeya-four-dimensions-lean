import Submission.Obl.k4_balanced_native_packet_transport.Native
import Submission.Obl.k4_balanced_native_packet_transport.Tracking

/-!
# Native samples as a tracked depth-zero known sequence

The localized native systems of the hypothesis are full-time (`T = 0`) charts
at depth zero with the native polynomial and terminal lists. Along losses
`1 / (n + 1)` they form one known sequence of the accepted o184 kind. The
tracked normalization then produces the balanced covered packets of x0351 inside
unchanged native charts.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport.TrackingNative

open MeasureTheory Filter Set
open Submission.Obl.k4_balanced_native_packet_transport.CPF.BalancedPacketSystems

abbrev SData := Submission.Obl.k4_remainder_pure_profile_normalization.Data
abbrev SAtlas := Submission.Obl.k4_remainder_pure_profile_normalization.Atlas
abbrev SKnownSequence := Submission.Obl.k4_remainder_pure_profile_normalization.KnownSequence

/-- The accepted o184 data of a frozen length-one problem. -/
def toData (N K : ℕ → ℝ) (d S η : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure Traj)
    (E : (k : ℕ) → Fin (W k) → Set Inc) (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ)
    (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ)
    (g : (k : ℕ) → Fin (W k) → ℝ → Obs → ENNReal)
    (G : (k : ℕ) → Fin (W k) → ℝ → (Obs × (Fin 2 → ℤ)) → ENNReal) : SData :=
  ⟨N, K, 1, d, S, η, W, ω, ν, E, P, B, f, g, G⟩

theorem toData_valid {N K : ℕ → ℝ} {d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure Traj}
    {E : (k : ℕ) → Fin (W k) → Set Inc} {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Obs → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → (Obs × (Fin 2 → ℤ)) → ENNReal}
    (h : Submission.Obl.k4_finite_width_output_exclusion.prob N K 1 d S η W ω ν E P B f g G) :
    (toData N K d S η W ω ν E P B f g G).Valid := h

/-- The o184 atlas formed by all charts of a native sample, with slack `κ` and
the native polynomial as chart test. -/
def nativeAtlas (p : SData) (k : ℕ) (σ : NativeSample (p.W k)) (κ : ℝ) : SAtlas p k where
  κ := κ
  T := σ.T
  C := σ.C
  γ := σ.γ
  j := σ.j
  c := σ.c
  u := σ.u
  Q := σ.Q
  R := fun a => p.P k (σ.γ a)
  A := σ.A
  F := σ.F

/-- A localized native sample is a known atlas at depth zero, with slack
`N ^ loss` and full time `T = 0`. -/
theorem nativeAtlas_knownAt {N K : ℕ → ℝ} {d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure Traj}
    {E : (k : ℕ) → Fin (W k) → Set Inc} {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Obs → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → (Obs × (Fin 2 → ℤ)) → ENNReal}
    {M D : ℕ} {a₀ w loss χ ds s m S' U : ℝ} (k : ℕ) (hN : 0 < N k) (σ : NativeSample (W k))
    (hσ : σ.Holds false (N k) (K k) (ω k) (ν k) (E k) (P k) (B k) M D a₀ w loss 1 χ ds s m S' U) :
    (nativeAtlas (toData N K d S η W ω ν E P B f g G) k σ (N k ^ loss)).KnownAt M D 0 ∧
      σ.T = 0 ∧ K k ≤ N k ^ loss := by
  obtain ⟨hK, _, hC, hsep, hlst, _, hchart, _, _, hlaw, hcover, _, hnat⟩ := hσ
  have hT : σ.T = 0 := hnat.1
  refine ⟨⟨σ.lst, hC, hsep, hlst, fun b => hchart b, ?_⟩, hT, hK⟩
  have hdom : ∀ a, ENNReal.ofReal (ω k (σ.γ a)) *
      (ENNReal.ofReal (1 / (2 : ℝ) ^ σ.T) * ν k (σ.γ a) (σ.A a)) * σ.law a Set.univ ≤
      ENNReal.ofReal (ω k (σ.γ a)) * ((ν k (σ.γ a)).prod volume) (σ.F a) := by
    intro a
    obtain ⟨_, _, _, _, _, _, hle⟩ := hlaw a
    have hmeas : Measurable (fun z : Inc =>
        (z.1, ((σ.j a : ℕ) : ℝ) / (2 : ℝ) ^ σ.T + 1 / (2 : ℝ) ^ σ.T * z.2)) := by fun_prop
    have h1 := (Measure.le_iff'.mp hle) Set.univ
    rw [Measure.smul_apply, Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul] at h1
    rw [mul_assoc]
    exact mul_le_mul' le_rfl h1
  have hinv : ENNReal.ofReal (N k ^ loss)⁻¹ = ENNReal.ofReal (N k ^ (-loss)) := by
    rw [Real.rpow_neg hN.le]
  show ENNReal.ofReal (N k ^ loss)⁻¹ ≤
    ∑ b, ENNReal.ofReal (ω k (σ.γ b)) * ((ν k (σ.γ b)).prod volume) (σ.F b)
  rw [hinv]
  exact hcover.trans (Finset.sum_le_sum fun a _ => hdom a)

/-- Along losses `1 / (n + 1)`, the native samples form one depth-zero,
time-zero known sequence whose atlases are exactly the native atlases. -/
theorem native_sequence {N K : ℕ → ℝ} {d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure Traj}
    {E : (k : ℕ) → Fin (W k) → Set Inc} {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Obs → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → (Obs × (Fin 2 → ℤ)) → ENNReal}
    (hN : ∀ k, 2 ≤ N k)
    {M D : ℕ} {a₀ w χ ds s m S' U : ℝ}
    (hsamples : ∀ loss : ℝ, 0 < loss → ∃ᶠ k in atTop,
      NativeSystemSample false (N k) (K k) (W k) (ω k) (ν k) (E k) (P k) (B k)
        M D a₀ w loss 1 χ ds s m S' U) :
    ∃ (ψ : ℕ → ℕ) (σ : (n : ℕ) → NativeSample (W (ψ n))), StrictMono ψ ∧
      (∀ n, (σ n).Holds false (N (ψ n)) (K (ψ n)) (ω (ψ n)) (ν (ψ n)) (E (ψ n)) (P (ψ n))
        (B (ψ n)) M D a₀ w (1 / ((n : ℝ) + 1)) 1 χ ds s m S' U) ∧
      ∃ s₀ : SKnownSequence (toData N K d S η W ω ν E P B f g G) M D 0 0,
        ∀ n, s₀.index n = ψ n ∧
          Tracking.SubOf (s₀.atlas n) (nativeAtlas (toData N K d S η W ω ν E P B f g G)
            (ψ n) (σ n) (N (ψ n) ^ (1 / ((n : ℝ) + 1)))) := by
  classical
  have hf : ∀ n : ℕ, ∃ᶠ k in atTop, ∃ σ : NativeSample (W k),
      σ.Holds false (N k) (K k) (ω k) (ν k) (E k) (P k) (B k) M D a₀ w
        (1 / ((n : ℝ) + 1)) 1 χ ds s m S' U := fun n =>
    (hsamples _ (by positivity)).mono fun k hk => nativeSystemSample_iff.mp hk
  obtain ⟨ψ, hψ, hψgood⟩ := Filter.extraction_forall_of_frequently hf
  choose σ hσ using hψgood
  have hknown := fun n => nativeAtlas_knownAt (d := d) (S := S) (η := η) (f := f) (g := g)
    (G := G) (ψ n) (by linarith [hN (ψ n)]) (σ n) (hσ n)
  have hεlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let s₀ : SKnownSequence (toData N K d S η W ω ν E P B f g G) M D 0 0 := {
    index := ψ
    strictMono := hψ
    atlas := fun n => nativeAtlas (toData N K d S η W ω ν E P B f g G) (ψ n) (σ n)
      (N (ψ n) ^ (1 / ((n : ℝ) + 1)))
    slack_one := fun n => Real.one_le_rpow (by linarith [hN (ψ n)]) (by positivity)
    slack_ambient := fun n => (hknown n).2.2
    slack_subpower := fun ε hε => by
      filter_upwards [hεlim.eventually (gt_mem_nhds hε)] with n hn
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [hN (ψ n)]) hn.le
    time_upper := fun ε hε => Filter.Eventually.of_forall fun n => by
      change (2 : ℝ) ^ (σ n).T ≤ N (ψ n) ^ ((0 : ℝ) + ε)
      rw [(hknown n).2.1, pow_zero]
      exact Real.one_le_rpow (by linarith [hN (ψ n)]) (by linarith)
    valid := fun n => (hknown n).1 }
  exact ⟨ψ, σ, hψ, hσ, s₀, fun n => ⟨rfl, Tracking.SubOf.refl _⟩⟩

/-- The frozen initial horizon bound in the expanded form used by the ported
x0351 sources. -/
theorem initialHorizonExpanded_of_initialRaw (hI : initialRaw) :
    CPF.InitialHorizonExpanded :=
  fun N K L d S η W ω ν E P B f g G hp h hh => hI N K L d S η W ω ν E P B f g G hp h hh

/-- The frozen extremal setup in the expanded form used by the ported sources. -/
theorem extremalSetup_of_es {ds kr S η : ℝ}
    (hes : Submission.Obl.k4_finite_width_output_exclusion.es ds kr S η) :
    CPF.ExtremalSetup ds kr S η := hes

/-- The frozen horizon of a length-one problem is the calibrated horizon of its
o184 data. -/
theorem horizon_toData {N K : ℕ → ℝ} {d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure Traj}
    {E : (k : ℕ) → Fin (W k) → Set Inc} {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Obs → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → (Obs × (Fin 2 → ℤ)) → ENNReal} :
    Submission.Obl.k4_finite_width_output_exclusion.H N K 1 W ω ν E B f =
      CPF.CalibratedHorizon.horizon (toData N K d S η W ω ν E P B f g G) :=
  CPF.ExtremalPacketProfiles.source_horizonExpanded_eq (toData N K d S η W ω ν E P B f g G)

/-- Move a native sample along an equality of original sample indices. -/
theorem transport_native {N K : ℕ → ℝ} {d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure Traj}
    {E : (k : ℕ) → Fin (W k) → Set Inc} {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Obs → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → (Obs × (Fin 2 → ℤ)) → ENNReal}
    {M D : ℕ} {a₀ w ℓ χ ds s m S' U : ℝ} {k k' : ℕ} (h : k = k')
    (σ : NativeSample (W k'))
    (hσ : σ.Holds false (N k') (K k') (ω k') (ν k') (E k') (P k') (B k') M D a₀ w ℓ 1 χ ds s m S' U)
    (a : SAtlas (toData N K d S η W ω ν E P B f g G) k)
    (ha : Tracking.SubOf a (nativeAtlas (toData N K d S η W ω ν E P B f g G) k' σ (N k' ^ ℓ))) :
    ∃ σ' : NativeSample (W k),
      σ'.Holds false (N k) (K k) (ω k) (ν k) (E k) (P k) (B k) M D a₀ w ℓ 1 χ ds s m S' U ∧
      Tracking.SubOf a (nativeAtlas (toData N K d S η W ω ν E P B f g G) k σ' (N k ^ ℓ)) := by
  subst h
  exact ⟨σ, hσ, ha⟩

/-- T1-T3 combined. For every sufficiently close maximizing length-one problem
with localized native samples, the samples along losses `1 / (n + 1)` carry a
calibrated remainder whose parent charts are unchanged native charts, and the
balanced covered systems of x0351 (`exists_balanced_covered_systems`) inside it.
The relative profile of the original problem is returned as well. -/
theorem tracked_native_packets (hI : initialRaw)
    {ds kr S η b Dcap err : ℝ}
    (hes : Submission.Obl.k4_finite_width_output_exclusion.es ds kr S η)
    (hb : 0 < b) (hb₁ : 2 * b ≤ 1) (herr : 0 < err)
    (hD : 0 < Dcap) (hD₁ : Dcap < 1) (hdD : ds < Dcap)
    (hsmall : 2 * err ≤ (Dcap - ds) * b) :
    ∃ tolerance : ℝ, 0 < tolerance ∧
    ∀ (N K : ℕ → ℝ) (d : ℝ) (W : ℕ → ℕ)
      (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure Traj)
      (E : (k : ℕ) → Fin (W k) → Set Inc) (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ)
      (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ)
      (g : (k : ℕ) → Fin (W k) → ℝ → Obs → ENNReal)
      (G : (k : ℕ) → Fin (W k) → ℝ → (Obs × (Fin 2 → ℤ)) → ENNReal),
      Submission.Obl.k4_finite_width_output_exclusion.prob N K 1 d S η W ω ν E P B f g G →
      d < ds + tolerance →
      kr - tolerance < Submission.Obl.k4_finite_width_output_exclusion.H N K 1 W ω ν E B f →
      ∀ {M D : ℕ} {a₀ w χ s m S' U : ℝ},
      (∀ loss : ℝ, 0 < loss → ∃ᶠ k in atTop,
        NativeSystemSample false (N k) (K k) (W k) (ω k) (ν k) (E k) (P k) (B k)
          M D a₀ w loss 1 χ ds s m S' U) →
      ∃ (ψ : ℕ → ℕ) (σ : (n : ℕ) → NativeSample (W (ψ n))), StrictMono ψ ∧
        (∀ n, (σ n).Holds false (N (ψ n)) (K (ψ n)) (ω (ψ n)) (ν (ψ n)) (E (ψ n)) (P (ψ n))
          (B (ψ n)) M D a₀ w (1 / ((n : ℝ) + 1)) 1 χ ds s m S' U) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, |f r - f 0 - ds * r| ≤ err) ∧
        ∃ q : Certificate (toData N K d S η W ω ν E P B f g G),
          (∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ n, q.sequence.index n = ψ (θ n) ∧
            Tracking.SubOf (q.sequence.atlas n)
              (nativeAtlas (toData N K d S η W ω ν E P B f g G) (ψ (θ n)) (σ (θ n))
                (N (ψ (θ n)) ^ (1 / ((θ n : ℝ) + 1))))) ∧
          (∀ n, ∃ (σ' : NativeSample (W (q.sequence.index n))) (ℓ : ℝ),
            0 < ℓ ∧ ℓ ≤ 1 / ((n : ℝ) + 1) ∧
            σ'.Holds false (N (q.sequence.index n)) (K (q.sequence.index n))
              (ω (q.sequence.index n)) (ν (q.sequence.index n)) (E (q.sequence.index n))
              (P (q.sequence.index n)) (B (q.sequence.index n)) M D a₀ w ℓ 1 χ ds s m S' U ∧
            Tracking.SubOf (q.sequence.atlas n)
              (nativeAtlas (toData N K d S η W ω ν E P B f g G) (q.sequence.index n) σ'
                (N (q.sequence.index n) ^ ℓ))) ∧
          ∃ r ∈ Icc b (2 * b), ∀ h : ℝ, 2 * b < h →
            ∃ M₁ D₁ : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
              ∃ a : CPF.Atlas (normalizedData q) k,
                1 ≤ a.κ ∧ (normalizedData q).K k ≤ a.κ ∧
                a.κ ≤ (normalizedData q).N k ^ ε ∧
                (2 : ℝ) ^ a.T ≤ (normalizedData q).N k ^ h ∧ a.SaturatedAt M₁ D₁ r ∧
                ENNReal.ofReal (N (q.sequence.index k) ^ (-ε)) ≤
                  CPF.OriginalPacketCoverage.originalCoveredMass q k a ∧
                ∀ c, MeasurableSet (originalAssignment q k a c) ∧
                  MeasurableSet (CPF.OriginalPacketCoverage.originalEvent q k a c) ∧
                  CPF.OriginalPacketCoverage.originalEvent q k a c ⊆
                    E (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c)) ∧
                  CPF.OriginalPacketCoverage.originalEvent q k a c ⊆
                    originalAssignment q k a c ×ˢ (univ : Set ℝ) ∧
                  N (q.sequence.index k) ^ (-ds * r - (3 * err + ε)) ≤
                    originalMass q k a c /
                      (N (q.sequence.index k) ^ (-f 0) * |(composedFrame q k a c).det|) ∧
                  originalMass q k a c /
                      (N (q.sequence.index k) ^ (-f 0) * |(composedFrame q k a c).det|) ≤
                    N (q.sequence.index k) ^ (-ds * r + (3 * err + ε)) := by
  obtain ⟨tolerance, htol, hpackets⟩ :=
    Tracking.tracked_packets (initialHorizonExpanded_of_initialRaw hI)
      (extremalSetup_of_es hes) hb hb₁ herr hD hD₁ hdD hsmall
  refine ⟨tolerance, htol, fun N K d W ω ν E P B f g G hprob hd hH M D a₀ w χ s m S' U
    hsamples => ?_⟩
  obtain ⟨ψ, σ, hψ, hσ, s₀, hs₀⟩ :=
    native_sequence (d := d) (S := S) (η := η) (f := f) (g := g) (G := G) hprob.1 hsamples
  have hnear : kr - tolerance <
      CPF.CalibratedHorizon.horizon (toData N K d S η W ω ν E P B f g G) := by
    rw [← horizon_toData]
    exact hH
  obtain ⟨hold, q, ⟨θ, hθ, hq⟩, hrest⟩ := hpackets (toData N K d S η W ω ν E P B f g G)
    (toData_valid hprob) rfl rfl rfl hd hnear s₀
  have hsub : ∀ n, q.sequence.index n = ψ (θ n) ∧
      Tracking.SubOf (q.sequence.atlas n)
        (nativeAtlas (toData N K d S η W ω ν E P B f g G) (ψ (θ n)) (σ (θ n))
          (N (ψ (θ n)) ^ (1 / ((θ n : ℝ) + 1)))) := fun n =>
    ⟨(hq n).1.trans (hs₀ (θ n)).1, (hq n).2.trans (hs₀ (θ n)).2⟩
  refine ⟨ψ, σ, hψ, hσ, hold, q, ⟨θ, hθ, hsub⟩, fun n => ?_, hrest⟩
  obtain ⟨σ', hσ', hsub'⟩ := transport_native (hsub n).1 (σ (θ n)) (hσ (θ n))
    (q.sequence.atlas n) (hsub n).2
  refine ⟨σ', 1 / ((θ n : ℝ) + 1), by positivity, ?_, hσ', hsub'⟩
  have hn : (n : ℝ) ≤ θ n := by exact_mod_cast hθ.id_le n
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

end Submission.Obl.k4_balanced_native_packet_transport.TrackingNative
